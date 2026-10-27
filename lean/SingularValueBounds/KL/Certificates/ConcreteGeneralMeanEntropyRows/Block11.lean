import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block09
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block13
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block14
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block16
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 770. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0770
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4985549663) (.branch 2 (.leaf 4812780490) (.leaf 4647782947))) (.branch 5 (.branch 4 (.leaf 4490112281) (.leaf 4339355240)) (.branch 6 (.leaf 4195127325) (.leaf 4057070335)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3924850171) (.leaf 3798154863)) (.branch 10 (.leaf 3676692797) (.leaf 3560191111))) (.branch 13 (.branch 12 (.leaf 3448394244) (.leaf 3341062622)) (.branch 14 (.leaf 3237971469) (.leaf 3138909708))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3043678982) (.branch 17 (.leaf 2952092738) (.leaf 2863975400))) (.branch 20 (.branch 19 (.leaf 2779161610) (.leaf 2697495526)) (.branch 21 (.leaf 2618830181) (.leaf 2543026891)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2469954709) (.leaf 2399489922)) (.branch 25 (.leaf 2331515582) (.leaf 2265921079))) (.branch 28 (.branch 27 (.leaf 2202601739) (.leaf 2141458456)) (.branch 29 (.leaf 2082397346) (.leaf 2025329425)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1970170321) (.branch 32 (.leaf 1916839987) (.leaf 1865262449))) (.branch 35 (.branch 34 (.leaf 1815365566) (.leaf 1767080804)) (.branch 36 (.leaf 1720343027) (.leaf 1675090304)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1631263722) (.leaf 1588807218)) (.branch 40 (.leaf 1547667421) (.leaf 1507793495))) (.branch 43 (.branch 42 (.leaf 1469137007) (.leaf 1431651790)) (.branch 44 (.leaf 1395293819) (.leaf 1360021100))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1325793556) (.branch 47 (.leaf 1292572925) (.leaf 1260322667))) (.branch 50 (.branch 49 (.leaf 1229007873) (.leaf 1198595176)) (.branch 51 (.leaf 1169052673) (.leaf 1140349854)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1112457522) (.leaf 1085347734)) (.branch 55 (.leaf 1058993732) (.leaf 1033369890))) (.branch 58 (.branch 57 (.leaf 1008451649) (.leaf 984215473)) (.branch 59 (.leaf 960638791) (.leaf 937699957))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 915378199) (.branch 62 (.leaf 893653580) (.leaf 872506958))) (.branch 65 (.branch 64 (.leaf 851919946) (.leaf 831874880)) (.branch 66 (.leaf 812354782) (.leaf 793343329)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 774824822) (.leaf 756784159)) (.branch 70 (.leaf 739206808) (.leaf 722078776))) (.branch 73 (.branch 72 (.leaf 705386591) (.leaf 689117277)) (.branch 74 (.leaf 673258330) (.leaf 657797698))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 642723762) (.branch 77 (.leaf 628025317) (.leaf 613691553))) (.branch 80 (.branch 79 (.leaf 599712040) (.leaf 586076709)) (.branch 81 (.leaf 572775841) (.leaf 559800046)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 547140255) (.leaf 534787706)) (.branch 85 (.leaf 522733928) (.leaf 510970731))) (.branch 88 (.branch 87 (.leaf 499490197) (.leaf 488284663)) (.branch 89 (.leaf 477346718) (.leaf 466669189)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 456245131) (.branch 92 (.leaf 446067821) (.leaf 436130746))) (.branch 95 (.branch 94 (.leaf 426427598) (.leaf 416952264)) (.branch 96 (.leaf 407698821) (.leaf 398661526)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 389834811) (.leaf 381213276)) (.branch 100 (.leaf 372791682) (.leaf 364564948))) (.branch 103 (.branch 102 (.leaf 356528141) (.leaf 348676477)) (.branch 104 (.leaf 341005307) (.leaf 333510119))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 326186532) (.leaf 319030289)) (.branch 108 (.leaf 312037255) (.leaf 305203412))) (.branch 111 (.branch 110 (.leaf 298524855) (.leaf 291997788)) (.branch 112 (.leaf 285618520) (.leaf 279383464)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 273289130) (.leaf 267332124)) (.branch 116 (.leaf 261509143) (.leaf 255816976))) (.branch 119 (.branch 118 (.leaf 250252495) (.leaf 244812658)) (.branch 120 (.leaf 239494505) (.leaf 234295150)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 770).prefactor = (2433946841444229/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 770).cutoff/(generalMeanRows 770).c)).2 =
    (187672749752023/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 770).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 770).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 770).q*(generalMeanRows 770).c/2-2 = (1699/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable222.value]
    have hcontinuation : (generalMeanRows 770).q*(generalMeanRows 770).cutoff/2-2 = (7982/3717:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable245.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 770).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 770

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 770).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 770).criticalRate j.val*(generalMeanRows 770).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 770).c*(generalMeanRows 770).criticalPoint j.val)).2-
      (generalMeanRows 770).J/2-(generalMeanRows 770).error (generalMeanGrid j.val)+
      (generalMeanRows 770).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 770).c)).2-
      (generalMeanRows 770).J/2-(generalMeanRows 770).error 4 := by
  have he : (generalMeanRows 770).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 770) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 770)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0770

/-! Kernel-checked entropy margins for general spectral rectangle 771. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0771
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5220063148) (.branch 2 (.leaf 5051561082) (.leaf 4890497182))) (.branch 5 (.branch 4 (.leaf 4736443120) (.leaf 4589001125)) (.branch 6 (.leaf 4447801312) (.leaf 4312499298)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4182774065) (.leaf 4058326040)) (.branch 10 (.leaf 3938875374) (.leaf 3824160378))) (.branch 13 (.branch 12 (.leaf 3713936118) (.leaf 3607973132)) (.branch 14 (.leaf 3506056271) (.leaf 3407983641))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3313565636) (.branch 17 (.leaf 3222624060) (.leaf 3134991316))) (.branch 20 (.branch 19 (.leaf 3050509668) (.leaf 2969030563)) (.branch 21 (.leaf 2890414002) (.leaf 2814527970)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2741247902) (.leaf 2670456193)) (.branch 25 (.leaf 2602041750) (.leaf 2535899567))) (.branch 28 (.branch 27 (.leaf 2471930343) (.leaf 2410040121)) (.branch 29 (.leaf 2350139951) (.leaf 2292145586)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2235977188) (.branch 32 (.leaf 2181559066) (.leaf 2128819422))) (.branch 35 (.branch 34 (.leaf 2077690120) (.leaf 2028106471)) (.branch 36 (.leaf 1980007025) (.leaf 1933333390)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1888030050) (.leaf 1844044200)) (.branch 40 (.leaf 1801325595) (.leaf 1759826401))) (.branch 43 (.branch 42 (.leaf 1719501064) (.leaf 1680306179)) (.branch 44 (.leaf 1642200375) (.leaf 1605144199))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1569100015) (.branch 47 (.leaf 1534031905) (.leaf 1499905573))) (.branch 50 (.branch 49 (.leaf 1466688265) (.leaf 1434348680)) (.branch 51 (.leaf 1402856898) (.leaf 1372184306)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1342303530) (.leaf 1313188372)) (.branch 55 (.leaf 1284813748) (.leaf 1257155634))) (.branch 58 (.branch 57 (.leaf 1230191007) (.leaf 1203897802)) (.branch 59 (.leaf 1178254857) (.leaf 1153241872))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1128839367) (.branch 62 (.leaf 1105028640) (.leaf 1081791728))) (.branch 65 (.branch 64 (.leaf 1059111376) (.leaf 1036970998)) (.branch 66 (.leaf 1015354648) (.leaf 994246988)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 973633260) (.leaf 953499262)) (.branch 70 (.leaf 933831315) (.leaf 914616247))) (.branch 73 (.branch 72 (.leaf 895841364) (.leaf 877494432)) (.branch 74 (.leaf 859563653) (.leaf 842037649))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 824905439) (.branch 77 (.leaf 808156428) (.leaf 791780382))) (.branch 80 (.branch 79 (.leaf 775767420) (.leaf 760107993)) (.branch 81 (.leaf 744792873) (.leaf 729813139)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 715160163) (.leaf 700825598)) (.branch 85 (.leaf 686801369) (.leaf 673079656))) (.branch 88 (.branch 87 (.leaf 659652889) (.leaf 646513738)) (.branch 89 (.leaf 633655097) (.leaf 621070084)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 608752026) (.branch 92 (.leaf 596694450) (.leaf 584891083))) (.branch 95 (.branch 94 (.leaf 573335834) (.leaf 562022794)) (.branch 96 (.leaf 550946230) (.leaf 540100571)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 529480409) (.leaf 519080491)) (.branch 100 (.leaf 508895712) (.leaf 498921112))) (.branch 103 (.branch 102 (.leaf 489151867) (.leaf 479583288)) (.branch 104 (.leaf 470210816) (.leaf 461030013))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 452036565) (.leaf 443226270)) (.branch 108 (.leaf 434595041) (.leaf 426138897))) (.branch 111 (.branch 110 (.leaf 417853963) (.leaf 409736463)) (.branch 112 (.leaf 401782722) (.leaf 393989156)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 386352275) (.leaf 378868676)) (.branch 116 (.leaf 371535042) (.leaf 364348141))) (.branch 119 (.branch 118 (.leaf 357304818) (.leaf 350401998)) (.branch 120 (.leaf 343636683) (.leaf 337005944)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 771).prefactor = (2362063258535043/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 771).cutoff/(generalMeanRows 771).c)).2 =
    (415628280759493/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 771).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 771).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 771).q*(generalMeanRows 771).c/2-2 = (377/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable247.value]
    have hcontinuation : (generalMeanRows 771).q*(generalMeanRows 771).cutoff/2-2 = (7930/3649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable248.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 771).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 771

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 771).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 771).criticalRate j.val*(generalMeanRows 771).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 771).c*(generalMeanRows 771).criticalPoint j.val)).2-
      (generalMeanRows 771).J/2-(generalMeanRows 771).error (generalMeanGrid j.val)+
      (generalMeanRows 771).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 771).c)).2-
      (generalMeanRows 771).J/2-(generalMeanRows 771).error 4 := by
  have he : (generalMeanRows 771).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 771) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 771)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0771

/-! Kernel-checked entropy margins for general spectral rectangle 772. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0772
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5254147162) (.branch 2 (.leaf 5084544874) (.leaf 4922429320))) (.branch 5 (.branch 4 (.leaf 4767369373) (.leaf 4618964666)) (.branch 6 (.leaf 4476842900) (.leaf 4340657442)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4210085177) (.leaf 4084824578)) (.branch 10 (.leaf 3964593968) (.leaf 3849129949))) (.branch 13 (.branch 12 (.leaf 3738185988) (.leaf 3631531124)) (.branch 14 (.leaf 3528948805) (.leaf 3430235817))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3335201317) (.branch 17 (.leaf 3243665944) (.leaf 3155461008))) (.branch 20 (.branch 19 (.leaf 3070427744) (.leaf 2988416627)) (.branch 21 (.leaf 2909286745) (.leaf 2832905221)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2759146676) (.leaf 2687892738)) (.branch 25 (.leaf 2619031588) (.leaf 2552457535))) (.branch 28 (.branch 27 (.leaf 2488070629) (.leaf 2425776299)) (.branch 29 (.leaf 2365485015) (.leaf 2307111980)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2250576835) (.branch 32 (.leaf 2195803394) (.leaf 2142719390))) (.branch 35 (.branch 34 (.leaf 2091256244) (.leaf 2041348841)) (.branch 36 (.leaf 1992935334) (.leaf 1945956947)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1900357802) (.leaf 1856084750)) (.branch 40 (.leaf 1813087216) (.leaf 1771317057))) (.branch 43 (.branch 42 (.leaf 1730728418) (.leaf 1691277613)) (.branch 44 (.leaf 1652923000) (.leaf 1615624868))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1579345337) (.branch 47 (.leaf 1544048252) (.leaf 1509699095))) (.branch 50 (.branch 49 (.leaf 1476264897) (.leaf 1443714153)) (.branch 51 (.leaf 1412016748) (.leaf 1381143881)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1351068001) (.leaf 1321762738)) (.branch 55 (.leaf 1293202844) (.leaf 1265364138))) (.branch 58 (.branch 57 (.leaf 1238223448) (.leaf 1211758563)) (.branch 59 (.leaf 1185948184) (.leaf 1160771879))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1136210040) (.branch 62 (.leaf 1112243842) (.leaf 1088855207))) (.branch 65 (.branch 64 (.leaf 1066026765) (.leaf 1043741823)) (.branch 66 (.leaf 1021984331) (.leaf 1000738850)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 979990526) (.leaf 959725064)) (.branch 70 (.leaf 939928697) (.leaf 920588166))) (.branch 73 (.branch 72 (.leaf 901690694) (.leaf 883223967)) (.branch 74 (.leaf 865176110) (.leaf 847535671))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 830291598) (.branch 77 (.leaf 813433225) (.leaf 796950253))) (.branch 80 (.branch 79 (.leaf 780832735) (.leaf 765071061)) (.branch 81 (.leaf 749655943) (.leaf 734578400)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 719829748) (.leaf 705401587)) (.branch 85 (.leaf 691285787) (.leaf 677474479))) (.branch 88 (.branch 87 (.leaf 663960044) (.leaf 650735101)) (.branch 89 (.leaf 637792501) (.leaf 625125315)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 612726827) (.branch 92 (.leaf 600590523) (.leaf 588710086))) (.branch 95 (.branch 94 (.leaf 577079387) (.leaf 565692481)) (.branch 96 (.leaf 554543592) (.leaf 543627117)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 532937612) (.leaf 522469789)) (.branch 100 (.leaf 512218509) (.leaf 502178780))) (.branch 103 (.branch 102 (.leaf 492345748) (.leaf 482714692)) (.branch 104 (.leaf 473281022) (.leaf 464040275))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 454988104) (.leaf 446120283)) (.branch 108 (.leaf 437432697) (.leaf 428921339))) (.branch 111 (.branch 110 (.leaf 420582309) (.leaf 412411807)) (.branch 112 (.leaf 404406132) (.leaf 396561679)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 388874933) (.leaf 381342470)) (.branch 116 (.leaf 373960953) (.leaf 366727125))) (.branch 119 (.branch 118 (.leaf 359637813) (.leaf 352689922)) (.branch 120 (.leaf 345880433) (.leaf 339206399)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 772).prefactor = (4754972349999099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 772).cutoff/(generalMeanRows 772).c)).2 =
    (415628280759493/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 772).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 772).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 772).q*(generalMeanRows 772).c/2-2 = (377/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable247.value]
    have hcontinuation : (generalMeanRows 772).q*(generalMeanRows 772).cutoff/2-2 = (7930/3649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable248.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 772).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 772

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 772).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 772).criticalRate j.val*(generalMeanRows 772).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 772).c*(generalMeanRows 772).criticalPoint j.val)).2-
      (generalMeanRows 772).J/2-(generalMeanRows 772).error (generalMeanGrid j.val)+
      (generalMeanRows 772).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 772).c)).2-
      (generalMeanRows 772).J/2-(generalMeanRows 772).error 4 := by
  have he : (generalMeanRows 772).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 772) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 772)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0772

/-! Kernel-checked entropy margins for general spectral rectangle 773. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0773
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5691109337) (.branch 2 (.leaf 5506145611) (.leaf 5329268361))) (.branch 5 (.branch 4 (.leaf 5160020348) (.leaf 4997976544)) (.branch 6 (.leaf 4842741324) (.leaf 4693945950)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4551246331) (.leaf 4414321002)) (.branch 10 (.leaf 4282869314) (.leaf 4156609799))) (.branch 13 (.branch 12 (.leaf 4035278689) (.leaf 3918628579)) (.branch 14 (.leaf 3806427204) (.leaf 3698456336))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3594510770) (.branch 17 (.leaf 3494397398) (.leaf 3397934371))) (.branch 20 (.branch 19 (.leaf 3304950316) (.leaf 3215283628)) (.branch 21 (.leaf 3128781813) (.leaf 3045300887)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2964704820) (.leaf 2886865017)) (.branch 25 (.leaf 2811659851) (.leaf 2738974218))) (.branch 28 (.branch 27 (.leaf 2668699129) (.leaf 2600731336)) (.branch 29 (.leaf 2534972978) (.leaf 2471331254)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2409718122) (.branch 32 (.leaf 2350050013) (.leaf 2292247572))) (.branch 35 (.branch 34 (.leaf 2236235407) (.leaf 2181941861)) (.branch 36 (.leaf 2129298801) (.leaf 2078241413)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2028708017) (.leaf 1980639891)) (.branch 40 (.leaf 1933981105) (.leaf 1888678370))) (.branch 43 (.branch 42 (.leaf 1844680890) (.leaf 1801940230)) (.branch 44 (.leaf 1760410184) (.leaf 1720046661))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1680807568) (.branch 47 (.leaf 1642652705) (.leaf 1605543668))) (.branch 50 (.branch 49 (.leaf 1569443754) (.leaf 1534317871)) (.branch 51 (.leaf 1500132459) (.leaf 1466855407)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1434455984) (.leaf 1402904765)) (.branch 55 (.leaf 1372173570) (.leaf 1342235398))) (.branch 58 (.branch 57 (.leaf 1313064370) (.leaf 1284635675)) (.branch 59 (.leaf 1256925515) (.leaf 1229911060))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1203570396) (.branch 62 (.leaf 1177882487) (.leaf 1152827125))) (.branch 65 (.branch 64 (.leaf 1128384901) (.leaf 1104537159)) (.branch 66 (.leaf 1081265963) (.leaf 1058554067)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1036384877) (.leaf 1014742428)) (.branch 70 (.leaf 993611349) (.leaf 972976841))) (.branch 73 (.branch 72 (.leaf 952824646) (.leaf 933141028)) (.branch 74 (.leaf 913912748) (.leaf 895127039))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 876771592) (.branch 77 (.leaf 858834528) (.leaf 841304384))) (.branch 80 (.branch 79 (.leaf 824170097) (.leaf 807420982)) (.branch 81 (.leaf 791046719) (.leaf 775037337)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 759383198) (.leaf 744074986)) (.branch 85 (.leaf 729103691) (.leaf 714460599))) (.branch 88 (.branch 87 (.leaf 700137278) (.leaf 686125566)) (.branch 89 (.leaf 672417563) (.leaf 659005617)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 645882317) (.branch 92 (.leaf 633040484) (.leaf 620473158))) (.branch 95 (.branch 94 (.leaf 608173593) (.leaf 596135250)) (.branch 96 (.leaf 584351783) (.leaf 572817039)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 561525046) (.leaf 550470007)) (.branch 100 (.leaf 539646297) (.leaf 529048449))) (.branch 103 (.branch 102 (.leaf 518671159) (.leaf 508509269)) (.branch 104 (.leaf 498557770) (.leaf 488811794))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 479266607) (.leaf 469917606)) (.branch 108 (.leaf 460760316) (.leaf 451790383))) (.branch 111 (.branch 110 (.leaf 443003571) (.leaf 434395759)) (.branch 112 (.leaf 425962935) (.leaf 417701192)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 409606730) (.leaf 401675844)) (.branch 116 (.leaf 393904927) (.leaf 386290467))) (.branch 119 (.branch 118 (.leaf 378829039) (.leaf 371517307)) (.branch 120 (.leaf 364352019) (.leaf 357330006)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 773).prefactor = (156933535511697/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 773).cutoff/(generalMeanRows 773).c)).2 =
    (388470216531341/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 773).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 773).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 773).q*(generalMeanRows 773).c/2-2 = (1199/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable178.value]
    have hcontinuation : (generalMeanRows 773).q*(generalMeanRows 773).cutoff/2-2 = (15814/7697:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable236.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 773).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 773

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 773).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 773).criticalRate j.val*(generalMeanRows 773).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 773).c*(generalMeanRows 773).criticalPoint j.val)).2-
      (generalMeanRows 773).J/2-(generalMeanRows 773).error (generalMeanGrid j.val)+
      (generalMeanRows 773).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 773).c)).2-
      (generalMeanRows 773).J/2-(generalMeanRows 773).error 4 := by
  have he : (generalMeanRows 773).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 773) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 773)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0773

/-! Kernel-checked entropy margins for general spectral rectangle 774. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0774
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5175544566) (.branch 2 (.leaf 5006029506) (.leaf 4843999868))) (.branch 5 (.branch 4 (.leaf 4689026935) (.leaf 4540712455)) (.branch 6 (.leaf 4398685985) (.leaf 4262602511)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4132140322) (.leaf 4006999099)) (.branch 10 (.leaf 3886898195) (.leaf 3771575085))) (.branch 13 (.branch 12 (.leaf 3660783958) (.leaf 3554294450)) (.branch 14 (.leaf 3451890480) (.leaf 3353369203))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3258540049) (.branch 17 (.leaf 3167223840) (.leaf 3079251992))) (.branch 20 (.branch 19 (.leaf 2994465776) (.leaf 2912715641)) (.branch 21 (.leaf 2833860595) (.leaf 2757767628)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2684311186) (.leaf 2613372684)) (.branch 25 (.leaf 2544840056) (.leaf 2478607334))) (.branch 28 (.branch 27 (.leaf 2414574265) (.leaf 2352645954)) (.branch 29 (.leaf 2292732527) (.leaf 2234748829)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2178614128) (.branch 32 (.leaf 2124251857) (.leaf 2071589357))) (.branch 35 (.branch 34 (.leaf 2020557650) (.leaf 1971091223)) (.branch 36 (.leaf 1923127821) (.leaf 1876608264)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1831476266) (.leaf 1787678275)) (.branch 40 (.leaf 1745163314) (.leaf 1703882837))) (.branch 43 (.branch 42 (.leaf 1663790597) (.leaf 1624842515)) (.branch 44 (.leaf 1586996565) (.leaf 1550212658))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1514452538) (.branch 47 (.leaf 1479679687) (.leaf 1445859228))) (.branch 50 (.branch 49 (.leaf 1412957840) (.leaf 1380943677)) (.branch 51 (.leaf 1349786289) (.leaf 1319456548)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1289926585) (.leaf 1261169721)) (.branch 55 (.leaf 1233160408) (.leaf 1205874172))) (.branch 58 (.branch 57 (.leaf 1179287558) (.leaf 1153378080)) (.branch 59 (.leaf 1128124173) (.leaf 1103505147))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1079501145) (.branch 62 (.leaf 1056093103) (.leaf 1033262709))) (.branch 65 (.branch 64 (.leaf 1010992369) (.leaf 989265175)) (.branch 66 (.leaf 968064867) (.leaf 947375809)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 927182952) (.leaf 907471817)) (.branch 70 (.leaf 888228459) (.leaf 869439449))) (.branch 73 (.branch 72 (.leaf 851091847) (.leaf 833173182)) (.branch 74 (.leaf 815671430) (.leaf 798574996))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 781872691) (.branch 77 (.leaf 765553720) (.leaf 749607658))) (.branch 80 (.branch 79 (.leaf 734024441) (.leaf 718794346)) (.branch 81 (.leaf 703907978) (.leaf 689356255)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 675130397) (.leaf 661221912)) (.branch 85 (.leaf 647622584) (.leaf 634324464))) (.branch 88 (.branch 87 (.leaf 621319854) (.leaf 608601304)) (.branch 89 (.leaf 596161595) (.leaf 583993736)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 572090949) (.branch 92 (.leaf 560446667) (.leaf 549054522))) (.branch 95 (.branch 94 (.leaf 537908335) (.leaf 527002117)) (.branch 96 (.leaf 516330053) (.leaf 505886500)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 495665980) (.leaf 485663174)) (.branch 100 (.leaf 475872916) (.leaf 466290187))) (.branch 103 (.branch 102 (.leaf 456910109) (.leaf 447727943)) (.branch 104 (.leaf 438739082) (.leaf 429939046))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 421323476) (.leaf 412888135)) (.branch 108 (.leaf 404628901) (.leaf 396541759))) (.branch 111 (.branch 110 (.leaf 388622806) (.leaf 380868240)) (.branch 112 (.leaf 373274358) (.leaf 365837557)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 358554326) (.leaf 351421245)) (.branch 116 (.leaf 344434981) (.leaf 337592287))) (.branch 119 (.branch 118 (.leaf 330889999) (.leaf 324325032)) (.branch 120 (.leaf 317894378) (.leaf 311595103)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 774).prefactor = (473455126591647/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 774).cutoff/(generalMeanRows 774).c)).2 =
    (100674996279687/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 774).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 774).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 774).q*(generalMeanRows 774).c/2-2 = (3097/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable249.value]
    have hcontinuation : (generalMeanRows 774).q*(generalMeanRows 774).cutoff/2-2 = (15778/7339:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable250.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 774).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 774

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 774).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 774).criticalRate j.val*(generalMeanRows 774).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 774).c*(generalMeanRows 774).criticalPoint j.val)).2-
      (generalMeanRows 774).J/2-(generalMeanRows 774).error (generalMeanGrid j.val)+
      (generalMeanRows 774).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 774).c)).2-
      (generalMeanRows 774).J/2-(generalMeanRows 774).error 4 := by
  have he : (generalMeanRows 774).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 774) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 774)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0774

/-! Kernel-checked entropy margins for general spectral rectangle 775. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0775
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5506721830) (.branch 2 (.leaf 5320191384) (.leaf 5141876506))) (.branch 5 (.branch 4 (.leaf 4971315749) (.leaf 4808080006)) (.branch 6 (.leaf 4651769685) (.leaf 4502012196)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4358459694) (.leaf 4220787058)) (.branch 10 (.leaf 4088690078) (.leaf 3961883812))) (.branch 13 (.branch 12 (.leaf 3840101103) (.leaf 3723091241)) (.branch 14 (.leaf 3610618734) (.leaf 3502462208))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3398413384) (.branch 17 (.leaf 3298276161) (.leaf 3201865764))) (.branch 20 (.branch 19 (.leaf 3109007967) (.leaf 3019538384)) (.branch 21 (.leaf 2933301808) (.leaf 2850151610)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2769949181) (.leaf 2692563415)) (.branch 25 (.leaf 2617870236) (.leaf 2545752156))) (.branch 28 (.branch 27 (.leaf 2476097866) (.leaf 2408801858)) (.branch 29 (.leaf 2343764071) (.leaf 2280889566)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2220088220) (.branch 32 (.leaf 2161274442) (.leaf 2104366909))) (.branch 35 (.branch 34 (.leaf 2049288320) (.leaf 1995965162)) (.branch 36 (.leaf 1944327500) (.leaf 1894308770)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1845845595) (.leaf 1798877604)) (.branch 40 (.leaf 1753347272) (.leaf 1709199758))) (.branch 43 (.branch 42 (.leaf 1666382767) (.leaf 1624846407)) (.branch 44 (.leaf 1584543064) (.leaf 1545427281))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1507455644) (.branch 47 (.leaf 1470586674) (.leaf 1434780731))) (.branch 50 (.branch 49 (.leaf 1399999914) (.leaf 1366207974)) (.branch 51 (.leaf 1333370234) (.leaf 1301453501)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1270426001) (.leaf 1240257301)) (.branch 55 (.leaf 1210918248) (.leaf 1182380903))) (.branch 58 (.branch 57 (.leaf 1154618481) (.leaf 1127605297)) (.branch 59 (.leaf 1101316713) (.leaf 1075729087))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1050819724) (.branch 62 (.leaf 1026566835) (.leaf 1002949490))) (.branch 65 (.branch 64 (.leaf 979947582) (.leaf 957541785)) (.branch 66 (.leaf 935713521) (.leaf 914444923)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 893718805) (.leaf 873518630)) (.branch 70 (.leaf 853828481) (.leaf 834633032))) (.branch 73 (.branch 72 (.leaf 815917523) (.leaf 797667737)) (.branch 74 (.leaf 779869972) (.leaf 762511021))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 745578149) (.branch 77 (.leaf 729059076) (.leaf 712941954))) (.branch 80 (.branch 79 (.leaf 697215349) (.leaf 681868227)) (.branch 81 (.leaf 666889931) (.leaf 652270173)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 637999012) (.leaf 624066842)) (.branch 85 (.leaf 610464381) (.leaf 597182653))) (.branch 88 (.branch 87 (.leaf 584212979) (.leaf 571546966)) (.branch 89 (.leaf 559176491) (.leaf 547093695)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 535290970) (.branch 92 (.leaf 523760952) (.leaf 512496506))) (.branch 95 (.branch 94 (.leaf 501490724) (.leaf 490736911)) (.branch 96 (.leaf 480228581) (.leaf 469959445)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 459923408) (.leaf 450114558)) (.branch 100 (.leaf 440527161) (.leaf 431155654))) (.branch 103 (.branch 102 (.leaf 421994641) (.leaf 413038882)) (.branch 104 (.leaf 404283293) (.leaf 395722937))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 387353020) (.leaf 379168884)) (.branch 108 (.leaf 371166006) (.leaf 363339990))) (.branch 111 (.branch 110 (.leaf 355686565) (.leaf 348201578)) (.branch 112 (.leaf 340880993) (.leaf 333720884)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 326717436) (.leaf 319866935)) (.branch 116 (.leaf 313165770) (.leaf 306610427))) (.branch 119 (.branch 118 (.leaf 300197485) (.leaf 293923617)) (.branch 120 (.leaf 287785583) (.leaf 281780229)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 775).prefactor = (1267973539292731/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 775).cutoff/(generalMeanRows 775).c)).2 =
    (360510176588411/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 775).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 775).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 775).q*(generalMeanRows 775).c/2-2 = (6493/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable213.value]
    have hcontinuation : (generalMeanRows 775).q*(generalMeanRows 775).cutoff/2-2 = (3932/1935:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable229.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 775).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 775

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 775).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 775).criticalRate j.val*(generalMeanRows 775).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 775).c*(generalMeanRows 775).criticalPoint j.val)).2-
      (generalMeanRows 775).J/2-(generalMeanRows 775).error (generalMeanGrid j.val)+
      (generalMeanRows 775).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 775).c)).2-
      (generalMeanRows 775).J/2-(generalMeanRows 775).error 4 := by
  have he : (generalMeanRows 775).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 775) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 775)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0775

/-! Kernel-checked entropy margins for general spectral rectangle 776. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0776
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5001025365) (.branch 2 (.leaf 4830294396) (.leaf 4667165360))) (.branch 5 (.branch 4 (.leaf 4511205711) (.leaf 4362013468)) (.branch 6 (.leaf 4219214552) (.leaf 4082460398)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3951425829) (.leaf 3825807139)) (.branch 10 (.leaf 3705320374) (.leaf 3589699775))) (.branch 13 (.branch 12 (.leaf 3478696376) (.leaf 3372076725)) (.branch 14 (.leaf 3269621731) (.leaf 3171125604))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3076394901) (.branch 17 (.leaf 2985247639) (.leaf 2897512498))) (.branch 20 (.branch 19 (.leaf 2813028078) (.leaf 2731642225)) (.branch 21 (.leaf 2653211407) (.leaf 2577600140)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2504680462) (.leaf 2434331439)) (.branch 25 (.leaf 2366438720) (.leaf 2300894113))) (.branch 28 (.branch 27 (.leaf 2237595203) (.leaf 2176444991)) (.branch 29 (.leaf 2117351559) (.leaf 2060227763)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2004990942) (.branch 32 (.leaf 1951562654) (.leaf 1899868423))) (.branch 35 (.branch 34 (.leaf 1849837504) (.leaf 1801402672)) (.branch 36 (.leaf 1754500013) (.leaf 1709068736)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1665050998) (.leaf 1622391736)) (.branch 40 (.leaf 1581038509) (.leaf 1540941358))) (.branch 43 (.branch 42 (.leaf 1502052667) (.leaf 1464327031)) (.branch 44 (.leaf 1427721144) (.leaf 1392193678))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1357705184) (.branch 47 (.leaf 1324217987) (.leaf 1291696094))) (.branch 50 (.branch 49 (.leaf 1260105110) (.leaf 1229412148)) (.branch 51 (.leaf 1199585758) (.leaf 1170595846)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1142413612) (.leaf 1115011482)) (.branch 55 (.leaf 1088363043) (.leaf 1062442991))) (.branch 58 (.branch 57 (.leaf 1037227071) (.leaf 1012692028)) (.branch 59 (.leaf 988815557) (.leaf 965576259))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 942953595) (.branch 62 (.leaf 920927842) (.leaf 899480063))) (.branch 65 (.branch 64 (.leaf 878592059) (.leaf 858246344)) (.branch 66 (.leaf 838426104) (.leaf 819115172)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 800297991) (.leaf 781959596)) (.branch 70 (.leaf 764085577) (.leaf 746662061))) (.branch 73 (.branch 72 (.leaf 729675685) (.leaf 713113572)) (.branch 74 (.leaf 696963313) (.leaf 681212945))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 665850929) (.branch 77 (.leaf 650866137) (.leaf 636247828))) (.branch 80 (.branch 79 (.leaf 621985637) (.leaf 608069555)) (.branch 81 (.leaf 594489918) (.leaf 581237387)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 568302941) (.leaf 555677859)) (.branch 85 (.leaf 543353710) (.leaf 531322341))) (.branch 88 (.branch 87 (.leaf 519575864) (.leaf 508106648)) (.branch 89 (.leaf 496907308) (.leaf 485970695)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 475289886) (.branch 92 (.leaf 464858175) (.leaf 454669068))) (.branch 95 (.branch 94 (.leaf 444716270) (.leaf 434993682)) (.branch 96 (.leaf 425495391) (.leaf 416215661)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 407148933) (.leaf 398289812)) (.branch 100 (.leaf 389633063) (.leaf 381173607))) (.branch 103 (.branch 102 (.leaf 372906515) (.leaf 364826997)) (.branch 104 (.leaf 356930408) (.leaf 349212231))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 341668081) (.leaf 334293699)) (.branch 108 (.leaf 327084941) (.leaf 320037785))) (.branch 111 (.branch 110 (.leaf 313148317) (.leaf 306412734)) (.branch 112 (.leaf 299827336) (.leaf 293388525)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 287092802) (.leaf 280936761)) (.branch 116 (.leaf 274917089) (.leaf 269030561))) (.branch 119 (.branch 118 (.leaf 263274038) (.leaf 257644464)) (.branch 120 (.leaf 252138864) (.leaf 246754341)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 776).prefactor = (955434250147611/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 776).cutoff/(generalMeanRows 776).c)).2 =
    (75093488657623/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 776).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 776).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 776).q*(generalMeanRows 776).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 776).q*(generalMeanRows 776).cutoff/2-2 = (436/205:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable091.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 776).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 776

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 776).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 776).criticalRate j.val*(generalMeanRows 776).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 776).c*(generalMeanRows 776).criticalPoint j.val)).2-
      (generalMeanRows 776).J/2-(generalMeanRows 776).error (generalMeanGrid j.val)+
      (generalMeanRows 776).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 776).c)).2-
      (generalMeanRows 776).J/2-(generalMeanRows 776).error 4 := by
  have he : (generalMeanRows 776).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 776) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 776)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0776

/-! Kernel-checked entropy margins for general spectral rectangle 777. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0777
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5124316246) (.branch 2 (.leaf 4954078334) (.leaf 4791385993))) (.branch 5 (.branch 4 (.leaf 4635807438) (.leaf 4486941542)) (.branch 6 (.leaf 4344415154) (.leaf 4207880711)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4077014096) (.leaf 3951512720)) (.branch 10 (.leaf 3831093789) (.leaf 3715492743))) (.branch 13 (.branch 12 (.leaf 3604461848) (.leaf 3497768910)) (.branch 14 (.leaf 3395196115) (.leaf 3296538970))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3201605334) (.branch 17 (.leaf 3110214541) (.leaf 3022196582))) (.branch 20 (.branch 19 (.leaf 2937391376) (.leaf 2855648078)) (.branch 21 (.leaf 2776824463) (.leaf 2700786343)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2627407040) (.leaf 2556566892)) (.branch 25 (.leaf 2488152803) (.leaf 2422057822))) (.branch 28 (.branch 27 (.leaf 2358180754) (.leaf 2296425801)) (.branch 29 (.leaf 2236702225) (.leaf 2178924041)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2123009725) (.branch 32 (.leaf 2068881947) (.leaf 2016467317))) (.branch 35 (.branch 34 (.leaf 1965696159) (.leaf 1916502285)) (.branch 36 (.leaf 1868822795) (.leaf 1822597891)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1777770691) (.leaf 1734287072)) (.branch 40 (.leaf 1692095508) (.leaf 1651146926))) (.branch 43 (.branch 42 (.leaf 1611394574) (.leaf 1572793885)) (.branch 44 (.leaf 1535302367) (.leaf 1498879480))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1463486539) (.branch 47 (.leaf 1429086610) (.leaf 1395644418))) (.branch 50 (.branch 49 (.leaf 1363126260) (.leaf 1331499920)) (.branch 51 (.leaf 1300734596) (.leaf 1270800820)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1241670397) (.leaf 1213316334)) (.branch 55 (.leaf 1185712782) (.leaf 1158834977))) (.branch 58 (.branch 57 (.leaf 1132659187) (.leaf 1107162659)) (.branch 59 (.leaf 1082323572) (.leaf 1058120990))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1034534819) (.branch 62 (.leaf 1011545769) (.leaf 989135311))) (.branch 65 (.branch 64 (.leaf 967285642) (.leaf 945979653)) (.branch 66 (.leaf 925200895) (.leaf 904933544)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 885162380) (.leaf 865872750)) (.branch 70 (.leaf 847050551) (.leaf 828682197))) (.branch 73 (.branch 72 (.leaf 810754602) (.leaf 793255151)) (.branch 74 (.leaf 776171687) (.leaf 759492484))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 743206230) (.branch 77 (.leaf 727302010) (.leaf 711769290))) (.branch 80 (.branch 79 (.leaf 696597895) (.leaf 681778001)) (.branch 81 (.leaf 667300115) (.leaf 653155063)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 639333975) (.leaf 625828276)) (.branch 85 (.leaf 612629671) (.leaf 599730133))) (.branch 88 (.branch 87 (.leaf 587121894) (.leaf 574797435)) (.branch 89 (.leaf 562749474) (.leaf 550970957)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 539455051) (.branch 92 (.leaf 528195133) (.leaf 517184784))) (.branch 95 (.branch 94 (.leaf 506417779) (.leaf 495888083)) (.branch 96 (.leaf 485589838) (.leaf 475517363)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 465665144) (.leaf 456027826)) (.branch 100 (.leaf 446600213) (.leaf 437377255))) (.branch 103 (.branch 102 (.leaf 428354050) (.leaf 419525832)) (.branch 104 (.leaf 410887972) (.leaf 402435968))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 394165446) (.leaf 386072150)) (.branch 108 (.leaf 378151943) (.leaf 370400799))) (.branch 111 (.branch 110 (.leaf 362814801) (.leaf 355390138)) (.branch 112 (.leaf 348123101) (.leaf 341010079)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 334047555) (.leaf 327232106)) (.branch 116 (.leaf 320560398) (.leaf 314029181))) (.branch 119 (.branch 118 (.leaf 307635292) (.leaf 301375647)) (.branch 120 (.leaf 295247241) (.leaf 289247144)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 777).prefactor = (190638860952533/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 777).cutoff/(generalMeanRows 777).c)).2 =
    (395427225789669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 777).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 777).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 777).q*(generalMeanRows 777).c/2-2 = (1589/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable251.value]
    have hcontinuation : (generalMeanRows 777).q*(generalMeanRows 777).cutoff/2-2 = (15778/7339:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable250.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 777).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 777

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 777).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 777).criticalRate j.val*(generalMeanRows 777).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 777).c*(generalMeanRows 777).criticalPoint j.val)).2-
      (generalMeanRows 777).J/2-(generalMeanRows 777).error (generalMeanGrid j.val)+
      (generalMeanRows 777).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 777).c)).2-
      (generalMeanRows 777).J/2-(generalMeanRows 777).error 4 := by
  have he : (generalMeanRows 777).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 777) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 777)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0777

/-! Kernel-checked entropy margins for general spectral rectangle 778. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0778
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5158323131) (.branch 2 (.leaf 4986955456) (.leaf 4823183427))) (.branch 5 (.branch 4 (.leaf 4666572395) (.leaf 4516718569)) (.branch 6 (.leaf 4373246322) (.leaf 4235805785)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4104070691) (.leaf 3977736441)) (.branch 10 (.leaf 3856518364) (.leaf 3740150147))) (.branch 13 (.branch 12 (.leaf 3628382409) (.leaf 3520981416)) (.branch 14 (.leaf 3417727909) (.leaf 3318416038))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3222852388) (.branch 17 (.leaf 3130855091) (.leaf 3042253012))) (.branch 20 (.branch 19 (.leaf 2956885007) (.leaf 2874599230)) (.branch 21 (.leaf 2795252512) (.leaf 2718709774)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2644843498) (.leaf 2573533229)) (.branch 25 (.leaf 2504665118) (.leaf 2438131506))) (.branch 28 (.branch 27 (.leaf 2373830526) (.leaf 2311665744)) (.branch 29 (.leaf 2251545820) (.leaf 2193384199)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2137098814) (.branch 32 (.leaf 2082611823) (.leaf 2029849351))) (.branch 35 (.branch 34 (.leaf 1978741256) (.leaf 1929220912)) (.branch 36 (.leaf 1881225004) (.leaf 1834693334)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1789568644) (.leaf 1745796452)) (.branch 40 (.leaf 1703324888) (.leaf 1662104556))) (.branch 43 (.branch 42 (.leaf 1622088392) (.leaf 1583231535)) (.branch 44 (.leaf 1545491209) (.leaf 1508826606))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1473198785) (.branch 47 (.leaf 1438570565) (.leaf 1404906438))) (.branch 50 (.branch 49 (.leaf 1372172477) (.leaf 1340336253)) (.branch 51 (.leaf 1309366758) (.leaf 1279234331)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1249910587) (.leaf 1221368356)) (.branch 55 (.leaf 1193581616) (.leaf 1166525440))) (.branch 58 (.branch 57 (.leaf 1140175938) (.leaf 1114510206)) (.branch 59 (.leaf 1089506277) (.leaf 1065143077))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1041400380) (.branch 62 (.leaf 1018258766) (.leaf 995699583))) (.branch 65 (.branch 64 (.leaf 973704912) (.leaf 952257529)) (.branch 66 (.leaf 931340875) (.leaf 910939023)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 891036649) (.leaf 871619007)) (.branch 70 (.leaf 852671896) (.leaf 834181643))) (.branch 73 (.branch 72 (.leaf 816135073) (.leaf 798519490)) (.branch 74 (.leaf 781322654) (.leaf 764532761))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 748138425) (.branch 77 (.leaf 732128659) (.leaf 716492858))) (.branch 80 (.branch 79 (.leaf 701220780) (.leaf 686302536)) (.branch 81 (.leaf 671728569) (.leaf 657489645)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 643576835) (.leaf 629981507)) (.branch 85 (.leaf 616695311) (.leaf 603710167))) (.branch 88 (.branch 87 (.leaf 591018255) (.leaf 578612007)) (.branch 89 (.leaf 566484090) (.leaf 554627407)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543035077) (.branch 92 (.leaf 531700434) (.leaf 520617016))) (.branch 95 (.branch 94 (.leaf 509778558) (.leaf 499178982)) (.branch 96 (.leaf 488812394) (.leaf 478673075)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 468755472) (.leaf 459054198)) (.branch 100 (.leaf 449564019) (.leaf 440279855))) (.branch 103 (.branch 102 (.leaf 431196768) (.leaf 422309963)) (.branch 104 (.leaf 413614779) (.leaf 405106684))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 396781276) (.leaf 388634270)) (.branch 108 (.leaf 380661501) (.leaf 372858917))) (.branch 111 (.branch 110 (.leaf 365222576) (.leaf 357748641)) (.branch 112 (.leaf 350433377) (.leaf 343273150)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 336264420) (.leaf 329403741)) (.branch 116 (.leaf 322687757) (.leaf 316113197))) (.branch 119 (.branch 118 (.leaf 309676876) (.leaf 303375689)) (.branch 120 (.leaf 297206612) (.leaf 291166696)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 778).prefactor = (959520059665153/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 778).cutoff/(generalMeanRows 778).c)).2 =
    (395427225789669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 778).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 778).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 778).q*(generalMeanRows 778).c/2-2 = (1589/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable251.value]
    have hcontinuation : (generalMeanRows 778).q*(generalMeanRows 778).cutoff/2-2 = (15778/7339:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable250.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 778).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 778

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 778).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 778).criticalRate j.val*(generalMeanRows 778).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 778).c*(generalMeanRows 778).criticalPoint j.val)).2-
      (generalMeanRows 778).J/2-(generalMeanRows 778).error (generalMeanGrid j.val)+
      (generalMeanRows 778).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 778).c)).2-
      (generalMeanRows 778).J/2-(generalMeanRows 778).error 4 := by
  have he : (generalMeanRows 778).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 778) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 778)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0778

/-! Kernel-checked entropy margins for general spectral rectangle 779. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0779
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5034764256) (.branch 2 (.leaf 4862881469) (.leaf 4698651900))) (.branch 5 (.branch 4 (.leaf 4541640085) (.leaf 4391441333)) (.branch 6 (.leaf 4247679039) (.leaf 4110002288)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3978083708) (.leaf 3851617544)) (.branch 10 (.leaf 3730317928) (.leaf 3613917307))) (.branch 13 (.branch 12 (.leaf 3502165035) (.leaf 3394826086)) (.branch 14 (.leaf 3291679890) (.leaf 3192519270))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3097149475) (.branch 17 (.leaf 3005387298) (.leaf 2917060261))) (.branch 20 (.branch 19 (.leaf 2832005876) (.leaf 2750070962)) (.branch 21 (.leaf 2671111018) (.leaf 2594989649)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2521578025) (.leaf 2450754400)) (.branch 25 (.leaf 2382403650) (.leaf 2316416853))) (.branch 28 (.branch 27 (.leaf 2252690904) (.leaf 2191128148)) (.branch 29 (.leaf 2131636049) (.leaf 2074126872)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2018517403) (.branch 32 (.leaf 1964728667) (.leaf 1912685685))) (.branch 35 (.branch 34 (.leaf 1862317238) (.leaf 1813555646)) (.branch 36 (.leaf 1766336562) (.leaf 1720598788)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1676284090) (.leaf 1633337031)) (.branch 40 (.leaf 1591704819) (.leaf 1551337157))) (.branch 43 (.branch 42 (.leaf 1512186107) (.leaf 1474205960)) (.branch 44 (.leaf 1437353114) (.leaf 1401585967))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1366864799) (.branch 47 (.leaf 1333151684) (.leaf 1300410386))) (.branch 50 (.branch 49 (.leaf 1268606277) (.leaf 1237706248)) (.branch 51 (.leaf 1207678637) (.leaf 1178493148)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1150120786) (.leaf 1122533790)) (.branch 55 (.leaf 1095705570) (.leaf 1069610651))) (.branch 58 (.branch 57 (.leaf 1044224614) (.leaf 1019524048)) (.branch 59 (.leaf 995486497) (.leaf 972090418))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 949315132) (.branch 62 (.leaf 927140785) (.leaf 905548310))) (.branch 65 (.branch 64 (.leaf 884519388) (.leaf 864036413)) (.branch 66 (.leaf 844082458) (.leaf 824641246)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 805697118) (.leaf 787235004)) (.branch 70 (.leaf 769240400) (.leaf 751699338))) (.branch 73 (.branch 72 (.leaf 734598365) (.leaf 717924517)) (.branch 74 (.leaf 701665303) (.leaf 685808676))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 670343023) (.branch 77 (.leaf 655257137) (.leaf 640540207))) (.branch 80 (.branch 79 (.leaf 626181798) (.leaf 612171833)) (.branch 81 (.leaf 598500581) (.leaf 585158644)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 572136937) (.leaf 559426681)) (.branch 85 (.leaf 547019389) (.leaf 534906851))) (.branch 88 (.branch 87 (.leaf 523081127) (.leaf 511534536)) (.branch 89 (.leaf 500259641) (.leaf 489249245)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 478496379) (.branch 92 (.leaf 467994292) (.leaf 457736445))) (.branch 95 (.branch 94 (.leaf 447716502) (.leaf 437928321)) (.branch 96 (.leaf 428365950) (.leaf 419023616)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 409895721) (.leaf 400976832)) (.branch 100 (.leaf 392261682) (.leaf 383745155))) (.branch 103 (.branch 102 (.leaf 375422289) (.leaf 367288264)) (.branch 104 (.leaf 359338401) (.leaf 351568154))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 343973109) (.leaf 336548976)) (.branch 108 (.leaf 329291585) (.leaf 322196886))) (.branch 111 (.branch 110 (.leaf 315260939) (.leaf 308479915)) (.branch 112 (.leaf 301850090) (.leaf 295367840)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 289029644) (.leaf 282832072)) (.branch 116 (.leaf 276771788) (.leaf 270845547))) (.branch 119 (.branch 118 (.leaf 265050188) (.leaf 259382635)) (.branch 120 (.leaf 253839892) (.leaf 248419043)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 779).prefactor = (2404699966960093/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 779).cutoff/(generalMeanRows 779).c)).2 =
    (75093488657623/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 779).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 779).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 779).q*(generalMeanRows 779).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 779).q*(generalMeanRows 779).cutoff/2-2 = (436/205:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable091.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 779).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 779

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 779).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 779).criticalRate j.val*(generalMeanRows 779).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 779).c*(generalMeanRows 779).criticalPoint j.val)).2-
      (generalMeanRows 779).J/2-(generalMeanRows 779).error (generalMeanGrid j.val)+
      (generalMeanRows 779).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 779).c)).2-
      (generalMeanRows 779).J/2-(generalMeanRows 779).error 4 := by
  have he : (generalMeanRows 779).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 779) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 779)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0779

/-! Kernel-checked entropy margins for general spectral rectangle 780. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0780
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4987011445) (.branch 2 (.leaf 4814474945) (.leaf 4649652332))) (.branch 5 (.branch 4 (.leaf 4492104905) (.leaf 4341424933)) (.branch 6 (.leaf 4197232957) (.leaf 4059175373)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3926922274) (.leaf 3800165516)) (.branch 10 (.leaf 3678616968) (.leaf 3562006943))) (.branch 13 (.branch 12 (.leaf 3450082771) (.leaf 3342607511)) (.branch 14 (.leaf 3239358773) (.leaf 3140127657))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3044717774) (.branch 17 (.leaf 2952944359) (.leaf 2864633451))) (.branch 20 (.branch 19 (.leaf 2779621154) (.leaf 2697752945)) (.branch 21 (.leaf 2618883044) (.leaf 2542873834)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2469595327) (.leaf 2398924663)) (.branch 25 (.leaf 2330745661) (.leaf 2264948388))) (.branch 28 (.branch 27 (.leaf 2201428773) (.leaf 2140088237)) (.branch 29 (.leaf 2080833362) (.leaf 2023575571)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1968230840) (.branch 32 (.leaf 1914719427) (.leaf 1862965612))) (.branch 35 (.branch 34 (.leaf 1812897470) (.leaf 1764446644)) (.branch 36 (.leaf 1717548143) (.leaf 1672140147)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1628163829) (.leaf 1585563186)) (.branch 40 (.leaf 1544284880) (.leaf 1504278095))) (.branch 43 (.branch 42 (.leaf 1465494394) (.leaf 1427887590)) (.branch 44 (.leaf 1391413625) (.leaf 1356030457))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1321697950) (.branch 47 (.leaf 1288377773) (.leaf 1256033308))) (.branch 50 (.branch 49 (.leaf 1224629557) (.leaf 1194133062)) (.branch 51 (.leaf 1164511821) (.leaf 1135735216)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1107773943) (.leaf 1080599947)) (.branch 55 (.leaf 1054186354) (.leaf 1028507420))) (.branch 58 (.branch 57 (.leaf 1003538467) (.leaf 979255836)) (.branch 59 (.leaf 955636838) (.leaf 932659702))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 910303534) (.branch 62 (.leaf 888548276) (.leaf 867374664))) (.branch 65 (.branch 64 (.leaf 846764191) (.leaf 826699074)) (.branch 66 (.leaf 807162215) (.leaf 788137176)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 769608143) (.leaf 751559900)) (.branch 70 (.leaf 733977803) (.leaf 716847750))) (.branch 73 (.branch 72 (.leaf 700156164) (.leaf 683889960)) (.branch 74 (.leaf 668036533) (.leaf 652583730))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 637519835) (.branch 77 (.leaf 622833545) (.leaf 608513958))) (.branch 80 (.branch 79 (.leaf 594550551) (.leaf 580933169)) (.branch 81 (.leaf 567652003) (.leaf 554697583)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 542060756) (.leaf 529732680)) (.branch 85 (.leaf 517704808) (.leaf 505968876))) (.branch 88 (.branch 87 (.leaf 494516892) (.leaf 483341126)) (.branch 89 (.leaf 472434096) (.leaf 461788565)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 451397524) (.branch 92 (.leaf 441254187) (.leaf 431351985))) (.branch 95 (.branch 94 (.leaf 421684551) (.leaf 412245717)) (.branch 96 (.leaf 403029506) (.leaf 394030124)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 385241952) (.leaf 376659544)) (.branch 100 (.leaf 368277615) (.leaf 360091039))) (.branch 103 (.branch 102 (.leaf 352094841) (.leaf 344284195)) (.branch 104 (.leaf 336654413) (.leaf 329200946))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 321919375) (.leaf 314805409)) (.branch 108 (.leaf 307854881) (.leaf 301063738))) (.branch 111 (.branch 110 (.leaf 294428046) (.leaf 287943979)) (.branch 112 (.leaf 281607819) (.leaf 275415950)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 269364857) (.leaf 263451122)) (.branch 116 (.leaf 257671418) (.leaf 252022510))) (.branch 119 (.branch 118 (.leaf 246501251) (.leaf 241104577)) (.branch 120 (.leaf 235829508) (.leaf 230673142)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 780).prefactor = (2420923022261127/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 780).cutoff/(generalMeanRows 780).c)).2 =
    (368349975519251/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 780).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 780).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 780).q*(generalMeanRows 780).c/2-2 = (3421/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable252.value]
    have hcontinuation : (generalMeanRows 780).q*(generalMeanRows 780).cutoff/2-2 = (436/205:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable091.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 780).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 780

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 780).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 780).criticalRate j.val*(generalMeanRows 780).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 780).c*(generalMeanRows 780).criticalPoint j.val)).2-
      (generalMeanRows 780).J/2-(generalMeanRows 780).error (generalMeanGrid j.val)+
      (generalMeanRows 780).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 780).c)).2-
      (generalMeanRows 780).J/2-(generalMeanRows 780).error 4 := by
  have he : (generalMeanRows 780).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 780) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 780)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0780

/-! Kernel-checked entropy margins for general spectral rectangle 781. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0781
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5063839741) (.branch 2 (.leaf 4893221975) (.leaf 4730220864))) (.branch 5 (.branch 4 (.leaf 4574398990) (.leaf 4425350046)) (.branch 6 (.leaf 4282696119) (.leaf 4146085260)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4015189317) (.leaf 3889701978)) (.branch 10 (.leaf 3769337023) (.leaf 3653826731))) (.branch 13 (.branch 12 (.leaf 3542920449) (.leaf 3436383294)) (.branch 14 (.leaf 3333994966) (.leaf 3235548679))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3140850172) (.branch 17 (.leaf 3049716817) (.leaf 2961976797))) (.branch 20 (.branch 19 (.leaf 2877468353) (.leaf 2796039093)) (.branch 21 (.leaf 2717545355) (.leaf 2641851625)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2568829995) (.leaf 2498359665)) (.branch 25 (.leaf 2430326482) (.leaf 2364622518))) (.branch 28 (.branch 27 (.leaf 2301145669) (.leaf 2239799296)) (.branch 29 (.leaf 2180491880) (.leaf 2123136710)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2067651590) (.branch 32 (.leaf 2013958562) (.leaf 1961983657))) (.branch 35 (.branch 34 (.leaf 1911656656) (.leaf 1862910870)) (.branch 36 (.leaf 1815682930) (.leaf 1769912600)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1725542595) (.leaf 1682518412)) (.branch 40 (.leaf 1640788172) (.leaf 1600302475))) (.branch 43 (.branch 42 (.leaf 1561014259) (.leaf 1522878672)) (.branch 44 (.leaf 1485852953) (.leaf 1449896313))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1414969831) (.branch 47 (.leaf 1381036356) (.leaf 1348060406))) (.branch 50 (.branch 49 (.leaf 1316008086) (.leaf 1284847001)) (.branch 51 (.leaf 1254546179) (.leaf 1225075996)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1196408106) (.leaf 1168515377)) (.branch 55 (.leaf 1141371830) (.leaf 1114952577))) (.branch 58 (.branch 57 (.leaf 1089233770) (.leaf 1064192549)) (.branch 59 (.leaf 1039806988) (.leaf 1016056056))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 992919569) (.branch 62 (.leaf 970378150) (.leaf 948413191))) (.branch 65 (.branch 64 (.leaf 927006813) (.leaf 906141836)) (.branch 66 (.leaf 885801742) (.leaf 865970646)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 846633267) (.leaf 827774898)) (.branch 70 (.leaf 809381382) (.leaf 791439083))) (.branch 73 (.branch 72 (.leaf 773934868) (.leaf 756856080)) (.branch 74 (.leaf 740190519) (.leaf 723926422))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 708052440) (.branch 77 (.leaf 692557624) (.leaf 677431408))) (.branch 80 (.branch 79 (.leaf 662663589) (.leaf 648244315)) (.branch 81 (.leaf 634164066) (.leaf 620413645)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 606984161) (.leaf 593867018)) (.branch 85 (.leaf 581053902) (.leaf 568536769))) (.branch 88 (.branch 87 (.leaf 556307836) (.leaf 544359570)) (.branch 89 (.leaf 532684675) (.leaf 521276088)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 510126964) (.branch 92 (.leaf 499230672) (.leaf 488580785))) (.branch 95 (.branch 94 (.leaf 478171073) (.leaf 467995494)) (.branch 96 (.leaf 458048187) (.leaf 448323468)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 438815819) (.leaf 429519888)) (.branch 100 (.leaf 420430474) (.leaf 411542533))) (.branch 103 (.branch 102 (.leaf 402851160) (.leaf 394351595)) (.branch 104 (.leaf 386039211) (.leaf 377909511))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 369958126) (.leaf 362180806)) (.branch 108 (.leaf 354573419) (.leaf 347131948))) (.branch 111 (.branch 110 (.leaf 339852485) (.leaf 332731226)) (.branch 112 (.leaf 325764472) (.leaf 318948621)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 312280168) (.leaf 305755701)) (.branch 116 (.leaf 299371897) (.leaf 293125519))) (.branch 119 (.branch 118 (.leaf 287013417) (.leaf 281032520)) (.branch 120 (.leaf 275179836) (.leaf 269452451)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 781).prefactor = (192690781905579/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 781).cutoff/(generalMeanRows 781).c)).2 =
    (98452308341213/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 781).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 781).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 781).q*(generalMeanRows 781).c/2-2 = (3259/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable253.value]
    have hcontinuation : (generalMeanRows 781).q*(generalMeanRows 781).cutoff/2-2 = (7930/3649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable248.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 781).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 781

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 781).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 781).criticalRate j.val*(generalMeanRows 781).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 781).c*(generalMeanRows 781).criticalPoint j.val)).2-
      (generalMeanRows 781).J/2-(generalMeanRows 781).error (generalMeanGrid j.val)+
      (generalMeanRows 781).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 781).c)).2-
      (generalMeanRows 781).J/2-(generalMeanRows 781).error 4 := by
  have he : (generalMeanRows 781).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 781) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 781)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0781

/-! Kernel-checked entropy margins for general spectral rectangle 782. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0782
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5130183560) (.branch 2 (.leaf 4957330448) (.leaf 4792193780))) (.branch 5 (.branch 4 (.leaf 4634330408) (.leaf 4483328702)) (.branch 6 (.leaf 4338805797) (.leaf 4200405133)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4067794258) (.leaf 3940662850)) (.branch 10 (.leaf 3818720935) (.leaf 3701697286))) (.branch 13 (.branch 12 (.leaf 3589337967) (.leaf 3481405017)) (.branch 14 (.leaf 3377675251) (.leaf 3277939171))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3181999972) (.branch 17 (.leaf 3089672635) (.leaf 3000783091))) (.branch 20 (.branch 19 (.leaf 2915167461) (.leaf 2832671356)) (.branch 21 (.leaf 2753149234) (.leaf 2676463804)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2602485482) (.leaf 2531091886)) (.branch 25 (.leaf 2462167368) (.leaf 2395602584))) (.branch 28 (.branch 27 (.leaf 2331294094) (.leaf 2269143992)) (.branch 29 (.leaf 2209059561) (.leaf 2150952953)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2094740895) (.branch 32 (.leaf 2040344409) (.leaf 1987688556))) (.branch 35 (.branch 34 (.leaf 1936702197) (.leaf 1887317768)) (.branch 36 (.leaf 1839471072) (.leaf 1793101083)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1748149765) (.leaf 1704561902)) (.branch 40 (.leaf 1662284934) (.leaf 1621268813))) (.branch 43 (.branch 42 (.leaf 1581465863) (.leaf 1542830644)) (.branch 44 (.leaf 1505319833) (.leaf 1468892107))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1433508037) (.branch 47 (.leaf 1399129982) (.leaf 1365721999))) (.branch 50 (.branch 49 (.leaf 1333249746) (.leaf 1301680405)) (.branch 51 (.leaf 1270982597) (.leaf 1241126310)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1212082828) (.leaf 1183824663)) (.branch 55 (.leaf 1156325495) (.leaf 1129560111))) (.branch 58 (.branch 57 (.leaf 1103504350) (.leaf 1078135051)) (.branch 59 (.leaf 1053430003) (.leaf 1029367899))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1005928289) (.branch 62 (.leaf 983091545) (.leaf 960838811))) (.branch 65 (.branch 64 (.leaf 939151978) (.leaf 918013639)) (.branch 66 (.leaf 897407060) (.leaf 877316147)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 857725420) (.leaf 838619979)) (.branch 70 (.leaf 819985479) (.leaf 801808110))) (.branch 73 (.branch 72 (.leaf 784074563) (.leaf 766772018)) (.branch 74 (.leaf 749888114) (.leaf 733410933))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 717328978) (.branch 77 (.leaf 701631157) (.leaf 686306766))) (.branch 80 (.branch 79 (.leaf 671345466) (.leaf 656737278)) (.branch 81 (.leaf 642472557) (.leaf 628541985)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 614936555) (.leaf 601647557)) (.branch 85 (.leaf 588666570) (.leaf 575985445))) (.branch 88 (.branch 87 (.leaf 563596295) (.leaf 551491489)) (.branch 89 (.leaf 539663636) (.leaf 528105579)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 516810384) (.branch 92 (.leaf 505771335) (.leaf 494981919))) (.branch 95 (.branch 94 (.leaf 484435824) (.leaf 474126930)) (.branch 96 (.leaf 464049298) (.leaf 454197171)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 444564958) (.leaf 435147236)) (.branch 100 (.leaf 425938738) (.leaf 416934351))) (.branch 103 (.branch 102 (.leaf 408129108) (.leaf 399518187)) (.branch 104 (.leaf 391096898) (.leaf 382860687))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 374805127) (.leaf 366925912)) (.branch 108 (.leaf 359218857) (.leaf 351679892))) (.branch 111 (.branch 110 (.leaf 344305057) (.leaf 337090499)) (.branch 112 (.leaf 330032470) (.leaf 323127321)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 316371502) (.leaf 309761555)) (.branch 116 (.leaf 303294113) (.leaf 296965899))) (.branch 119 (.branch 118 (.leaf 290773719) (.leaf 284714463)) (.branch 120 (.leaf 278785100) (.leaf 272982678)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 782).prefactor = (4880382931063529/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 782).cutoff/(generalMeanRows 782).c)).2 =
    (98452308341213/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 782).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 782).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 782).q*(generalMeanRows 782).c/2-2 = (3259/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable253.value]
    have hcontinuation : (generalMeanRows 782).q*(generalMeanRows 782).cutoff/2-2 = (7930/3649:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable248.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 782).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 782

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 782).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 782).criticalRate j.val*(generalMeanRows 782).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 782).c*(generalMeanRows 782).criticalPoint j.val)).2-
      (generalMeanRows 782).J/2-(generalMeanRows 782).error (generalMeanGrid j.val)+
      (generalMeanRows 782).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 782).c)).2-
      (generalMeanRows 782).J/2-(generalMeanRows 782).error 4 := by
  have he : (generalMeanRows 782).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 782) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 782)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0782

/-! Kernel-checked entropy margins for general spectral rectangle 783. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0783
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5197018832) (.branch 2 (.leaf 5028258429) (.leaf 4866938165))) (.branch 5 (.branch 4 (.leaf 4712630590) (.leaf 4564938721)) (.branch 6 (.leaf 4423493384) (.leaf 4287950833)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4157990622) (.leaf 4033313687)) (.branch 10 (.leaf 3913640633) (.leaf 3798710171))) (.branch 13 (.branch 12 (.leaf 3688277718) (.leaf 3582114121)) (.branch 14 (.leaf 3480004496) (.leaf 3381747176))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3287152748) (.branch 17 (.leaf 3196043174) (.leaf 3108250988))) (.branch 20 (.branch 19 (.leaf 3023618555) (.leaf 2941997396)) (.branch 21 (.leaf 2863247566) (.leaf 2787237078)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2713841376) (.leaf 2642942848)) (.branch 25 (.leaf 2574430373) (.leaf 2508198904))) (.branch 28 (.branch 27 (.leaf 2444149085) (.leaf 2382186888)) (.branch 29 (.leaf 2322223283) (.leaf 2264173930)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2207958891) (.branch 32 (.leaf 2153502363) (.leaf 2100732428))) (.branch 35 (.branch 34 (.leaf 2049580826) (.leaf 1999982733)) (.branch 36 (.leaf 1951876564) (.leaf 1905203781)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1859908720) (.leaf 1815938426)) (.branch 40 (.leaf 1773242497) (.leaf 1731772942))) (.branch 43 (.branch 42 (.leaf 1691484047) (.leaf 1652332244)) (.branch 44 (.leaf 1614275998) (.leaf 1577275693))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1541293525) (.branch 47 (.leaf 1506293410) (.leaf 1472240887))) (.branch 50 (.branch 49 (.leaf 1439103034) (.leaf 1406848384)) (.branch 51 (.leaf 1375446854) (.leaf 1344869663)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1315089277) (.leaf 1286079333)) (.branch 55 (.leaf 1257814587) (.leaf 1230270855))) (.branch 58 (.branch 57 (.leaf 1203424958) (.leaf 1177254672)) (.branch 59 (.leaf 1151738683) (.leaf 1126856539))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1102588609) (.branch 62 (.leaf 1078916043) (.leaf 1055820734))) (.branch 65 (.branch 64 (.leaf 1033285282) (.leaf 1011292961)) (.branch 66 (.leaf 989827686) (.leaf 968873983)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 948416962) (.leaf 928442288)) (.branch 70 (.leaf 908936156) (.leaf 889885266))) (.branch 73 (.branch 72 (.leaf 871276803) (.leaf 853098410)) (.branch 74 (.leaf 835338172) (.leaf 817984597))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 801026590) (.branch 77 (.leaf 784453446) (.leaf 768254824))) (.branch 80 (.branch 79 (.leaf 752420738) (.leaf 736941535)) (.branch 81 (.leaf 721807890) (.leaf 707010783)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 692541492) (.leaf 678391577)) (.branch 85 (.leaf 664552872) (.leaf 651017472))) (.branch 88 (.branch 87 (.leaf 637777721) (.leaf 624826205)) (.branch 89 (.leaf 612155741) (.leaf 599759366)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 587630332) (.branch 92 (.leaf 575762094) (.leaf 564148305))) (.branch 95 (.branch 94 (.leaf 552782807) (.leaf 541659625)) (.branch 96 (.leaf 530772957) (.leaf 520117173)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 509686803) (.leaf 499476536)) (.branch 100 (.leaf 489481208) (.leaf 479695806))) (.branch 103 (.branch 102 (.leaf 470115452) (.leaf 460735407)) (.branch 104 (.leaf 451551060) (.leaf 442557929))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 433751651) (.leaf 425127981)) (.branch 108 (.leaf 416682789) (.leaf 408412053))) (.branch 111 (.branch 110 (.leaf 400311859) (.leaf 392378393)) (.branch 112 (.leaf 384607943) (.leaf 376996892)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 369541714) (.leaf 362238976)) (.branch 116 (.leaf 355085330) (.leaf 348077512))) (.branch 119 (.branch 118 (.leaf 341212343) (.leaf 334486720)) (.branch 120 (.leaf 327897617) (.leaf 321442084)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 783).prefactor = (4745994540270049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 783).cutoff/(generalMeanRows 783).c)).2 =
    (205466076430199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 783).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 783).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 783).q*(generalMeanRows 783).c/2-2 = (77/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable254.value]
    have hcontinuation : (generalMeanRows 783).q*(generalMeanRows 783).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 783).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 783

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 783).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 783).criticalRate j.val*(generalMeanRows 783).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 783).c*(generalMeanRows 783).criticalPoint j.val)).2-
      (generalMeanRows 783).J/2-(generalMeanRows 783).error (generalMeanGrid j.val)+
      (generalMeanRows 783).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 783).c)).2-
      (generalMeanRows 783).J/2-(generalMeanRows 783).error 4 := by
  have he : (generalMeanRows 783).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 783) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 783)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0783

/-! Kernel-checked entropy margins for general spectral rectangle 784. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0784
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5264813110) (.branch 2 (.leaf 5093851254) (.leaf 4930426594))) (.branch 5 (.branch 4 (.leaf 4774106100) (.leaf 4624487614)) (.branch 6 (.leaf 4481197146) (.leaf 4343886464)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4212230943) (.leaf 4085927618)) (.branch 10 (.leaf 3964693447) (.leaf 3848263736))) (.branch 13 (.branch 12 (.leaf 3736390710) (.leaf 3628842226)) (.branch 14 (.leaf 3525400597) (.leaf 3425861526))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3330033128) (.branch 17 (.leaf 3237735045) (.leaf 3148797624))) (.branch 20 (.branch 19 (.leaf 3063061174) (.leaf 2980375281)) (.branch 21 (.leaf 2900598172) (.leaf 2823596139)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2749243002) (.leaf 2677419614)) (.branch 25 (.leaf 2608013404) (.leaf 2540917957))) (.branch 28 (.branch 27 (.leaf 2476032618) (.leaf 2413262134)) (.branch 29 (.leaf 2352516314) (.leaf 2293709716)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2236761361) (.branch 32 (.leaf 2181594456) (.leaf 2128136146))) (.branch 35 (.branch 34 (.leaf 2076317279) (.leaf 2026072187)) (.branch 36 (.leaf 1977338481) (.leaf 1930056859)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1884170931) (.leaf 1839627052)) (.branch 40 (.leaf 1796374161) (.leaf 1754363643))) (.branch 43 (.branch 42 (.leaf 1713549185) (.leaf 1673886654)) (.branch 44 (.leaf 1635333970) (.leaf 1597851001))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1561399452) (.branch 47 (.leaf 1525942766) (.leaf 1491446033))) (.branch 50 (.branch 49 (.leaf 1457875902) (.leaf 1425200496)) (.branch 51 (.leaf 1393389337) (.leaf 1362413272)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1332244405) (.leaf 1302856032)) (.branch 55 (.leaf 1274222577) (.leaf 1246319542))) (.branch 58 (.branch 57 (.leaf 1219123444) (.leaf 1192611771)) (.branch 59 (.leaf 1166762930) (.leaf 1141556202))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1116971701) (.branch 62 (.leaf 1092990330) (.leaf 1069593746))) (.branch 65 (.branch 64 (.leaf 1046764323) (.leaf 1024485115)) (.branch 66 (.leaf 1002739829) (.leaf 981512789)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 960788909) (.leaf 940553669)) (.branch 70 (.leaf 920793082) (.leaf 901493677))) (.branch 73 (.branch 72 (.leaf 882642469) (.leaf 864226942)) (.branch 74 (.leaf 846235025) (.leaf 828655075))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 811475854) (.branch 77 (.leaf 794686515) (.leaf 778276585))) (.branch 80 (.branch 79 (.leaf 762235945) (.leaf 746554820)) (.branch 81 (.leaf 731223759) (.leaf 716233626)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 701575584) (.leaf 687241086)) (.branch 85 (.leaf 673221857) (.leaf 659509890))) (.branch 88 (.branch 87 (.leaf 646097429) (.leaf 632976963)) (.branch 89 (.leaf 620141215) (.leaf 607583131)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 595295876) (.branch 92 (.leaf 583272818) (.leaf 571507529))) (.branch 95 (.branch 94 (.leaf 559993770) (.leaf 548725488)) (.branch 96 (.leaf 537696805) (.leaf 526902018)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 516335586) (.leaf 505992127)) (.branch 100 (.leaf 495866412) (.leaf 485953361))) (.branch 103 (.branch 102 (.leaf 476248033) (.leaf 466745626)) (.branch 104 (.leaf 457441472) (.leaf 448331026))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 439409871) (.leaf 430673707)) (.branch 108 (.leaf 422118349) (.leaf 413739723))) (.branch 111 (.branch 110 (.leaf 405533863) (.leaf 397496906)) (.branch 112 (.leaf 389625092) (.leaf 381914756)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 374362326) (.leaf 366964325)) (.branch 116 (.leaf 359717361) (.leaf 352618128))) (.branch 119 (.branch 118 (.leaf 345663404) (.leaf 338850045)) (.branch 120 (.leaf 332174989) (.leaf 325635244)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 784).prefactor = (4807905278255321/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 784).cutoff/(generalMeanRows 784).c)).2 =
    (205466076430199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 784).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 784).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 784).q*(generalMeanRows 784).c/2-2 = (77/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable254.value]
    have hcontinuation : (generalMeanRows 784).q*(generalMeanRows 784).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 784).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 784

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 784).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 784).criticalRate j.val*(generalMeanRows 784).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 784).c*(generalMeanRows 784).criticalPoint j.val)).2-
      (generalMeanRows 784).J/2-(generalMeanRows 784).error (generalMeanGrid j.val)+
      (generalMeanRows 784).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 784).c)).2-
      (generalMeanRows 784).J/2-(generalMeanRows 784).error 4 := by
  have he : (generalMeanRows 784).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 784) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 784)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0784

/-! Kernel-checked entropy margins for general spectral rectangle 785. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0785
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5076209207) (.branch 2 (.leaf 4904290552) (.leaf 4740039586))) (.branch 5 (.branch 4 (.leaf 4583016867) (.leaf 4432814182)) (.branch 6 (.leaf 4289051818) (.leaf 4151376129)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4019457350) (.leaf 3892987645)) (.branch 10 (.leaf 3771679341) (.leaf 3655263338))) (.branch 13 (.branch 12 (.leaf 3543487668) (.leaf 3436116190)) (.branch 14 (.leaf 3332927408) (.leaf 3233713383))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3138278757) (.branch 17 (.leaf 3046439846) (.leaf 2958023821))) (.branch 20 (.branch 19 (.leaf 2872867948) (.leaf 2790818899)) (.branch 21 (.leaf 2711732112) (.leaf 2635471202)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2561907425) (.leaf 2490919170)) (.branch 25 (.leaf 2422391506) (.leaf 2356215749))) (.branch 28 (.branch 27 (.leaf 2292289067) (.leaf 2230514114)) (.branch 29 (.leaf 2170798691) (.leaf 2113055425)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2057201478) (.branch 32 (.leaf 2003158275) (.leaf 1950851244))) (.branch 35 (.branch 34 (.leaf 1900209584) (.leaf 1851166039)) (.branch 36 (.leaf 1803656693) (.leaf 1757620779)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1713000493) (.leaf 1669740832)) (.branch 40 (.leaf 1627789431) (.leaf 1587096414))) (.branch 43 (.branch 42 (.leaf 1547614264) (.leaf 1509297681)) (.branch 44 (.leaf 1472103470) (.leaf 1435990422))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1400919208) (.branch 47 (.leaf 1366852277) (.leaf 1333753764))) (.branch 50 (.branch 49 (.leaf 1301589398) (.leaf 1270326418)) (.branch 51 (.leaf 1239933498) (.leaf 1210380670)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1181639254) (.leaf 1153681792)) (.branch 55 (.leaf 1126481989) (.leaf 1100014652))) (.branch 58 (.branch 57 (.leaf 1074255632) (.leaf 1049181779)) (.branch 59 (.leaf 1024770887) (.leaf 1001001651))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 977853621) (.branch 62 (.leaf 955307162) (.leaf 933343414))) (.branch 65 (.branch 64 (.leaf 911944255) (.leaf 891092269)) (.branch 66 (.leaf 870770708) (.leaf 850963464)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 831655039) (.leaf 812830516)) (.branch 70 (.leaf 794475532) (.leaf 776576256))) (.branch 73 (.branch 72 (.leaf 759119362) (.leaf 742092006)) (.branch 74 (.leaf 725481807) (.leaf 709276825))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 693465542) (.branch 77 (.leaf 678036846) (.leaf 662980008))) (.branch 80 (.branch 79 (.leaf 648284671) (.leaf 633940831)) (.branch 81 (.leaf 619938824) (.leaf 606269311)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 592923265) (.leaf 579891956)) (.branch 85 (.leaf 567166942) (.leaf 554740055))) (.branch 88 (.branch 87 (.leaf 542603391) (.leaf 530749301)) (.branch 89 (.leaf 519170376) (.leaf 507859443)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 496809553) (.branch 92 (.leaf 486013972) (.leaf 475466174))) (.branch 95 (.branch 94 (.leaf 465159834) (.leaf 455088818)) (.branch 96 (.leaf 445247175) (.leaf 435629135)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 426229098) (.leaf 417041630)) (.branch 100 (.leaf 408061455) (.leaf 399283450))) (.branch 103 (.branch 102 (.leaf 390702643) (.leaf 382314200)) (.branch 104 (.leaf 374113429) (.leaf 366095769))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 358256786) (.leaf 350592172)) (.branch 108 (.leaf 343097738) (.leaf 335769409))) (.branch 111 (.branch 110 (.leaf 328603225) (.leaf 321595330)) (.branch 112 (.leaf 314741975) (.leaf 308039512)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 301484390) (.leaf 295073151)) (.branch 116 (.leaf 288802432) (.leaf 282668956))) (.branch 119 (.branch 118 (.leaf 276669532) (.leaf 270801052)) (.branch 120 (.leaf 265060491) (.leaf 259444899)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 785).prefactor = (4870623631893199/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 785).cutoff/(generalMeanRows 785).c)).2 =
    (389502761404499/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 785).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 785).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 785).q*(generalMeanRows 785).c/2-2 = (83/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable255.value]
    have hcontinuation : (generalMeanRows 785).q*(generalMeanRows 785).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 785).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 785

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 785).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 785).criticalRate j.val*(generalMeanRows 785).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 785).c*(generalMeanRows 785).criticalPoint j.val)).2-
      (generalMeanRows 785).J/2-(generalMeanRows 785).error (generalMeanGrid j.val)+
      (generalMeanRows 785).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 785).c)).2-
      (generalMeanRows 785).J/2-(generalMeanRows 785).error 4 := by
  have he : (generalMeanRows 785).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 785) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 785)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0785

/-! Kernel-checked entropy margins for general spectral rectangle 786. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0786
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7647669781) (.branch 2 (.leaf 7425831787) (.leaf 7212745992))) (.branch 5 (.branch 4 (.leaf 7007956324) (.leaf 6811038049)) (.branch 6 (.leaf 6621594943) (.leaf 6439256787)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6263677139) (.leaf 6094531345)) (.branch 10 (.leaf 5931514770) (.leaf 5774341202))) (.branch 13 (.branch 12 (.leaf 5622741421) (.leaf 5476461909)) (.branch 14 (.leaf 5335263682) (.leaf 5198921232))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5067221567) (.branch 17 (.leaf 4939963334) (.leaf 4816956026))) (.branch 20 (.branch 19 (.leaf 4698019247) (.leaf 4582982047)) (.branch 21 (.leaf 4471682307) (.leaf 4363966179)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4259687561) (.leaf 4158707625)) (.branch 25 (.leaf 4060894370) (.leaf 3966122215))) (.branch 28 (.branch 27 (.leaf 3874271619) (.leaf 3785228733)) (.branch 29 (.leaf 3698885069) (.leaf 3615137198)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3533886468) (.branch 32 (.leaf 3455038739) (.leaf 3378504140))) (.branch 35 (.branch 34 (.leaf 3304196835) (.leaf 3232034810)) (.branch 36 (.leaf 3161939673) (.leaf 3093836463)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3027653474) (.leaf 2963322091)) (.branch 40 (.leaf 2900776631) (.leaf 2839954198))) (.branch 43 (.branch 42 (.leaf 2780794544) (.leaf 2723239939)) (.branch 44 (.leaf 2667235051) (.leaf 2612726828))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2559664387) (.branch 47 (.leaf 2507998918) (.leaf 2457683578))) (.branch 50 (.branch 49 (.leaf 2408673406) (.leaf 2360925233)) (.branch 51 (.leaf 2314397598) (.leaf 2269050674)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2224846192) (.leaf 2181747369)) (.branch 55 (.leaf 2139718847) (.leaf 2098726623))) (.branch 58 (.branch 57 (.leaf 2058737993) (.leaf 2019721498)) (.branch 59 (.leaf 1981646863) (.leaf 1944484950))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1908207709) (.branch 62 (.leaf 1872788132) (.leaf 1838200206))) (.branch 65 (.branch 64 (.leaf 1804418873) (.leaf 1771419990)) (.branch 66 (.leaf 1739180290) (.leaf 1707677346)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1676889536) (.leaf 1646796010)) (.branch 70 (.leaf 1617376658) (.leaf 1588612082))) (.branch 73 (.branch 72 (.leaf 1560483563) (.leaf 1532973039)) (.branch 74 (.leaf 1506063073) (.leaf 1479736832))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1453978063) (.branch 77 (.leaf 1428771067) (.leaf 1404100681))) (.branch 80 (.branch 79 (.leaf 1379952253) (.leaf 1356311626)) (.branch 81 (.leaf 1333165117) (.leaf 1310499496)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1288301975) (.leaf 1266560185)) (.branch 85 (.leaf 1245262163) (.leaf 1224396336))) (.branch 88 (.branch 87 (.leaf 1203951506) (.leaf 1183916836)) (.branch 89 (.leaf 1164281836) (.leaf 1145036353)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1126170553) (.branch 92 (.leaf 1107674914) (.leaf 1089540212))) (.branch 95 (.branch 94 (.leaf 1071757512) (.leaf 1054318155)) (.branch 96 (.leaf 1037213751) (.leaf 1020436164)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1003977511) (.leaf 987830144)) (.branch 100 (.leaf 971986649) (.leaf 956439833))) (.branch 103 (.branch 102 (.leaf 941182718) (.leaf 926208533)) (.branch 104 (.leaf 911510706) (.leaf 897082860))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 882918801) (.leaf 869012518)) (.branch 108 (.leaf 855358170) (.leaf 841950087))) (.branch 111 (.branch 110 (.leaf 828782757) (.leaf 815850827)) (.branch 112 (.leaf 803149093) (.leaf 790672499)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 778416127) (.leaf 766375198)) (.branch 116 (.leaf 754545061) (.leaf 742921196))) (.branch 119 (.branch 118 (.leaf 731499204) (.leaf 720274804)) (.branch 120 (.leaf 709243833) (.leaf 698402236)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 786).prefactor = (5030635125419257/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 786).cutoff/(generalMeanRows 786).c)).2 =
    (78801587499581/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 786).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 786).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 786).q*(generalMeanRows 786).c/2-2 = (139/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable113.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 786).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 786

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 786).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 786).criticalRate j.val*(generalMeanRows 786).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 786).c*(generalMeanRows 786).criticalPoint j.val)).2-
      (generalMeanRows 786).J/2-(generalMeanRows 786).error (generalMeanGrid j.val)+
      (generalMeanRows 786).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 786).c)).2-
      (generalMeanRows 786).J/2-(generalMeanRows 786).error 4 := by
  have he : (generalMeanRows 786).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 786) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 786)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0786

/-! Kernel-checked entropy margins for general spectral rectangle 787. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0787
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7024446105) (.branch 2 (.leaf 6824921796) (.leaf 6633407854))) (.branch 5 (.branch 4 (.leaf 6449478691) (.leaf 6272738023)) (.branch 6 (.leaf 6102816248) (.leaf 5939368130)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5782070733) (.leaf 5630621577)) (.branch 10 (.leaf 5484736984) (.leaf 5344150599))) (.branch 13 (.branch 12 (.leaf 5208612048) (.leaf 5077885737)) (.branch 14 (.leaf 4951749754) (.leaf 4829994882))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4712423694) (.branch 17 (.leaf 4598849731) (.leaf 4489096752))) (.branch 20 (.branch 19 (.leaf 4382998047) (.leaf 4280395806)) (.branch 21 (.leaf 4181140541) (.leaf 4085090552)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3992111439) (.leaf 3902075645)) (.branch 25 (.leaf 3814862041) (.leaf 3730355536))) (.branch 28 (.branch 27 (.leaf 3648446718) (.leaf 3569031523)) (.branch 29 (.leaf 3492010920) (.leaf 3417290628)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3344780843) (.branch 32 (.leaf 3274395992) (.leaf 3206054493))) (.branch 35 (.branch 34 (.leaf 3139678544) (.leaf 3075193912)) (.branch 36 (.leaf 3012529745) (.leaf 2951618392)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2892395235) (.leaf 2834798533)) (.branch 40 (.leaf 2778769268) (.leaf 2724251013))) (.branch 43 (.branch 42 (.leaf 2671189795) (.leaf 2619533976)) (.branch 44 (.leaf 2569234134) (.leaf 2520242953))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2472515123) (.branch 47 (.leaf 2426007239) (.leaf 2380677709))) (.branch 50 (.branch 49 (.leaf 2336486671) (.leaf 2293395906)) (.branch 51 (.leaf 2251368762) (.leaf 2210370080)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2170366126) (.leaf 2131324523)) (.branch 55 (.leaf 2093214187) (.leaf 2056005274))) (.branch 58 (.branch 57 (.leaf 2019669116) (.leaf 1984178171)) (.branch 59 (.leaf 1949505973) (.leaf 1915627085))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1882517048) (.branch 62 (.leaf 1850152343) (.leaf 1818510348))) (.branch 65 (.branch 64 (.leaf 1787569298) (.leaf 1757308246)) (.branch 66 (.leaf 1727707034) (.leaf 1698746250)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1670407204) (.leaf 1642671891)) (.branch 70 (.leaf 1615522967) (.leaf 1588943717))) (.branch 73 (.branch 72 (.leaf 1562918032) (.leaf 1537430380)) (.branch 74 (.leaf 1512465785) (.leaf 1488009803))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1464048497) (.branch 77 (.leaf 1440568424) (.leaf 1417556604))) (.branch 80 (.branch 79 (.leaf 1395000512) (.leaf 1372888052)) (.branch 81 (.leaf 1351207541) (.leaf 1329947695)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1309097613) (.leaf 1288646757)) (.branch 85 (.leaf 1268584943) (.leaf 1248902326))) (.branch 88 (.branch 87 (.leaf 1229589382) (.leaf 1210636903)) (.branch 89 (.leaf 1192035979) (.leaf 1173777987)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1155854584) (.branch 92 (.leaf 1138257691) (.leaf 1120979486))) (.branch 95 (.branch 94 (.leaf 1104012395) (.leaf 1087349078)) (.branch 96 (.leaf 1070982426) (.leaf 1054905548)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1039111765) (.leaf 1023594603)) (.branch 100 (.leaf 1008347781) (.leaf 993365209))) (.branch 103 (.branch 102 (.leaf 978640978) (.leaf 964169355)) (.branch 104 (.leaf 949944774) (.leaf 935961835))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 922215290) (.leaf 908700048)) (.branch 108 (.leaf 895411159) (.leaf 882343816))) (.branch 111 (.branch 110 (.leaf 869493347) (.leaf 856855211)) (.branch 112 (.leaf 844424995) (.leaf 832198405)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 820171267) (.leaf 808339519)) (.branch 116 (.leaf 796699210) (.leaf 785246495))) (.branch 119 (.branch 118 (.leaf 773977630) (.leaf 762888973)) (.branch 120 (.leaf 751976974) (.leaf 741238178)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 787).prefactor = (2349218604674089/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 787).cutoff/(generalMeanRows 787).c)).2 =
    (356978941509107/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 787).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 787).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 787).q*(generalMeanRows 787).c/2-2 = (53/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable031.value]
    have hcontinuation : (generalMeanRows 787).q*(generalMeanRows 787).cutoff/2-2 = (21/13:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable056.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 787).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 787

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 787).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 787).criticalRate j.val*(generalMeanRows 787).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 787).c*(generalMeanRows 787).criticalPoint j.val)).2-
      (generalMeanRows 787).J/2-(generalMeanRows 787).error (generalMeanGrid j.val)+
      (generalMeanRows 787).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 787).c)).2-
      (generalMeanRows 787).J/2-(generalMeanRows 787).error 4 := by
  have he : (generalMeanRows 787).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 787) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 787)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0787

/-! Kernel-checked entropy margins for general spectral rectangle 788. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0788
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6871619249) (.branch 2 (.leaf 6663814040) (.leaf 6464419460))) (.branch 5 (.branch 4 (.leaf 6272991027) (.leaf 6089114784)) (.branch 6 (.leaf 5912404570) (.leaf 5742499610)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5579062361) (.leaf 5421776589)) (.branch 10 (.leaf 5270345652) (.leaf 5124490953))) (.branch 13 (.branch 12 (.leaf 4983950549) (.leaf 4848477894)) (.branch 14 (.leaf 4717840700) (.leaf 4591819906))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4470208736) (.branch 17 (.leaf 4352811846) (.leaf 4239444542))) (.branch 20 (.branch 19 (.leaf 4129932062) (.leaf 4024108922)) (.branch 21 (.leaf 3921818310) (.leaf 3822911538)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3727247525) (.leaf 3634692330)) (.branch 25 (.leaf 3545118711) (.leaf 3458405726))) (.branch 28 (.branch 27 (.leaf 3374438360) (.leaf 3293107171)) (.branch 29 (.leaf 3214307974) (.leaf 3137941541)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3063913315) (.branch 32 (.leaf 2992133156) (.leaf 2922515095))) (.branch 35 (.branch 34 (.leaf 2854977108) (.leaf 2789440899)) (.branch 36 (.leaf 2725831708) (.leaf 2664078118)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2604111883) (.leaf 2545867765)) (.branch 40 (.leaf 2489283376) (.leaf 2434299036))) (.branch 43 (.branch 42 (.leaf 2380857636) (.leaf 2328904509)) (.branch 44 (.leaf 2278387310) (.leaf 2229255901))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2181462242) (.branch 47 (.leaf 2134960293) (.leaf 2089705915))) (.branch 50 (.branch 49 (.leaf 2045656783) (.leaf 2002772294)) (.branch 51 (.leaf 1961013494) (.leaf 1920342994)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1880724903) (.leaf 1842124754)) (.branch 55 (.leaf 1804509444) (.leaf 1767847169))) (.branch 58 (.branch 57 (.leaf 1732107365) (.leaf 1697260655)) (.branch 59 (.leaf 1663278794) (.leaf 1630134618))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1597802001) (.branch 62 (.leaf 1566255802) (.leaf 1535471830))) (.branch 65 (.branch 64 (.leaf 1505426797) (.leaf 1476098283)) (.branch 66 (.leaf 1447464696) (.leaf 1419505238)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1392199871) (.leaf 1365529287)) (.branch 70 (.leaf 1339474873) (.leaf 1314018686))) (.branch 73 (.branch 72 (.leaf 1289143424) (.leaf 1264832398)) (.branch 74 (.leaf 1241069509) (.leaf 1217839224))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1195126549) (.branch 77 (.leaf 1172917013) (.leaf 1151196643))) (.branch 80 (.branch 79 (.leaf 1129951944) (.leaf 1109169882)) (.branch 81 (.leaf 1088837865) (.leaf 1068943725)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1049475699) (.leaf 1030422420)) (.branch 85 (.leaf 1011772895) (.leaf 993516491))) (.branch 88 (.branch 87 (.leaf 975642924) (.leaf 958142247)) (.branch 89 (.leaf 941004830) (.leaf 924221355)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 907782802) (.branch 92 (.leaf 891680436) (.leaf 875905797))) (.branch 95 (.branch 94 (.leaf 860450692) (.leaf 845307183)) (.branch 96 (.leaf 830467577) (.leaf 815924419)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 801670481) (.leaf 787698758)) (.branch 100 (.leaf 774002452) (.leaf 760574973))) (.branch 103 (.branch 102 (.leaf 747409926) (.leaf 734501107)) (.branch 104 (.leaf 721842495) (.leaf 709428245))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 697252682) (.leaf 685310296)) (.branch 108 (.leaf 673595736) (.leaf 662103802))) (.branch 111 (.branch 110 (.leaf 650829446) (.leaf 639767758)) (.branch 112 (.leaf 628913968) (.leaf 618263440)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 607811665) (.leaf 597554259)) (.branch 116 (.leaf 587486957) (.leaf 577605613))) (.branch 119 (.branch 118 (.leaf 567906190) (.leaf 558384760)) (.branch 120 (.leaf 549037502) (.leaf 539860695)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 788).prefactor = (981912791487513/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 788).cutoff/(generalMeanRows 788).c)).2 =
    (32126085890703/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 788).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 788).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 788).q*(generalMeanRows 788).c/2-2 = (311/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable072.value]
    have hcontinuation : (generalMeanRows 788).q*(generalMeanRows 788).cutoff/2-2 = (21/13:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable056.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 788).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 788

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 788).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 788).criticalRate j.val*(generalMeanRows 788).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 788).c*(generalMeanRows 788).criticalPoint j.val)).2-
      (generalMeanRows 788).J/2-(generalMeanRows 788).error (generalMeanGrid j.val)+
      (generalMeanRows 788).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 788).c)).2-
      (generalMeanRows 788).J/2-(generalMeanRows 788).error 4 := by
  have he : (generalMeanRows 788).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 788) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 788)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0788

/-! Kernel-checked entropy margins for general spectral rectangle 789. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0789
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6683681768) (.branch 2 (.leaf 6483569045) (.leaf 6291622663))) (.branch 5 (.branch 4 (.leaf 6107406414) (.leaf 5930514121)) (.branch 6 (.leaf 5760566968) (.leaf 5597211136)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5440115691) (.leaf 5288970702)) (.branch 10 (.leaf 5143485550) (.leaf 5003387410))) (.branch 13 (.branch 12 (.leaf 4868419880) (.leaf 4738341745)) (.branch 14 (.leaf 4612925857) (.leaf 4491958116))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4375236541) (.branch 17 (.leaf 4262570431) (.leaf 4153779587))) (.branch 20 (.branch 19 (.leaf 4048693610) (.leaf 3947151246)) (.branch 21 (.leaf 3848999799) (.leaf 3754094575)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3662298379) (.leaf 3573481050)) (.branch 25 (.leaf 3487519027) (.leaf 3404294950))) (.branch 28 (.branch 27 (.leaf 3323697290) (.leaf 3245620006)) (.branch 29 (.leaf 3169962222) (.leaf 3096627933)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3025525728) (.branch 32 (.leaf 2956568530) (.leaf 2889673354))) (.branch 35 (.branch 34 (.leaf 2824761083) (.leaf 2761756260)) (.branch 36 (.leaf 2700586886) (.leaf 2641184237)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2583482691) (.leaf 2527419567)) (.branch 40 (.leaf 2472934969) (.leaf 2419971646))) (.branch 43 (.branch 42 (.leaf 2368474851) (.leaf 2318392223)) (.branch 44 (.leaf 2269673660) (.leaf 2222271209))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2176138958) (.branch 47 (.leaf 2131232940) (.leaf 2087511034))) (.branch 50 (.branch 49 (.leaf 2044932877) (.leaf 2003459779)) (.branch 51 (.leaf 1963054645) (.leaf 1923681897)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1885307404) (.leaf 1847898415)) (.branch 55 (.leaf 1811423491) (.leaf 1775852451))) (.branch 58 (.branch 57 (.leaf 1741156307) (.leaf 1707307213)) (.branch 59 (.leaf 1674278416) (.leaf 1642044201))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1610579847) (.branch 62 (.leaf 1579861584) (.leaf 1549866549))) (.branch 65 (.branch 64 (.leaf 1520572747) (.leaf 1491959011)) (.branch 66 (.leaf 1464004969) (.leaf 1436691006)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1409998234) (.leaf 1383908461)) (.branch 70 (.leaf 1358404157) (.leaf 1333468431))) (.branch 73 (.branch 72 (.leaf 1309085002) (.leaf 1285238172)) (.branch 74 (.leaf 1261912803) (.leaf 1239094293))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1216768556) (.branch 77 (.leaf 1194921997) (.leaf 1173541493))) (.branch 80 (.branch 79 (.leaf 1152614377) (.leaf 1132128414)) (.branch 81 (.leaf 1112071788) (.leaf 1092433083)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1073201267) (.leaf 1054365678)) (.branch 85 (.leaf 1035916008) (.leaf 1017842289))) (.branch 88 (.branch 87 (.leaf 1000134880) (.leaf 982784454)) (.branch 89 (.leaf 965781988) (.leaf 949118747)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 932786276) (.branch 92 (.leaf 916776389) (.leaf 901081157))) (.branch 95 (.branch 94 (.leaf 885692899) (.leaf 870604176)) (.branch 96 (.leaf 855807775) (.leaf 841296707)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 827064196) (.leaf 813103670)) (.branch 100 (.leaf 799408755) (.leaf 785973268))) (.branch 103 (.branch 102 (.leaf 772791210) (.leaf 759856757)) (.branch 104 (.leaf 747164257) (.leaf 734708222))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 722483322) (.leaf 710484381)) (.branch 108 (.leaf 698706369) (.leaf 687144399))) (.branch 111 (.branch 110 (.leaf 675793722) (.leaf 664649719)) (.branch 112 (.leaf 653707901) (.leaf 642963903)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 632413478) (.leaf 622052495)) (.branch 116 (.leaf 611876933) (.leaf 601882881))) (.branch 119 (.branch 118 (.leaf 592066530) (.leaf 582424172)) (.branch 120 (.leaf 572952197) (.leaf 563647088)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 789).prefactor = (4822338861335447/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 789).cutoff/(generalMeanRows 789).c)).2 =
    (343089829348441/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 789).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 789).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 789).q*(generalMeanRows 789).c/2-2 = (61/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable006.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 789).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 789

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 789).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 789).criticalRate j.val*(generalMeanRows 789).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 789).c*(generalMeanRows 789).criticalPoint j.val)).2-
      (generalMeanRows 789).J/2-(generalMeanRows 789).error (generalMeanGrid j.val)+
      (generalMeanRows 789).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 789).c)).2-
      (generalMeanRows 789).J/2-(generalMeanRows 789).error 4 := by
  have he : (generalMeanRows 789).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 789) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 789)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0789

/-! Kernel-checked entropy margins for general spectral rectangle 790. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0790
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6390284094) (.branch 2 (.leaf 6198622134) (.leaf 6014861783))) (.branch 5 (.branch 4 (.leaf 5838576444) (.leaf 5669368980)) (.branch 6 (.leaf 5506869109) (.leaf 5350731088)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5200631653) (.leaf 5056268172)) (.branch 10 (.leaf 4917356991) (.leaf 4783631945))) (.branch 13 (.branch 12 (.leaf 4654843013) (.leaf 4530755102)) (.branch 14 (.leaf 4411146949) (.leaf 4295810116))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4184548083) (.branch 17 (.leaf 4077175411) (.leaf 3973516985))) (.branch 20 (.branch 19 (.leaf 3873407319) (.leaf 3776689912)) (.branch 21 (.leaf 3683216664) (.leaf 3592847335)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3505449044) (.leaf 3420895810)) (.branch 25 (.leaf 3339068126) (.leaf 3259852565))) (.branch 28 (.branch 27 (.leaf 3183141412) (.leaf 3108832327)) (.branch 29 (.leaf 3036828027) (.leaf 2967035994)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2899368203) (.branch 32 (.leaf 2833740863) (.leaf 2770074181))) (.branch 35 (.branch 34 (.leaf 2708292141) (.leaf 2648322292)) (.branch 36 (.leaf 2590095560) (.leaf 2533546059)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2478610922) (.leaf 2425230144)) (.branch 40 (.leaf 2373346427) (.leaf 2322905041))) (.branch 43 (.branch 42 (.leaf 2273853692) (.leaf 2226142395)) (.branch 44 (.leaf 2179723355) (.leaf 2134550860))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2090581175) (.branch 47 (.leaf 2047772441) (.leaf 2006084586))) (.branch 50 (.branch 49 (.leaf 1965479234) (.leaf 1925919623)) (.branch 51 (.leaf 1887370529) (.leaf 1849798189)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1813170233) (.leaf 1777455615)) (.branch 55 (.leaf 1742624553) (.leaf 1708648470))) (.branch 58 (.branch 57 (.leaf 1675499936) (.leaf 1643152613)) (.branch 59 (.leaf 1611581211) (.leaf 1580761432))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1550669931) (.branch 62 (.leaf 1521284268) (.leaf 1492582870))) (.branch 65 (.branch 64 (.leaf 1464544992) (.leaf 1437150680)) (.branch 66 (.leaf 1410380734) (.leaf 1384216675)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1358640717) (.leaf 1333635731)) (.branch 70 (.leaf 1309185222) (.leaf 1285273298))) (.branch 73 (.branch 72 (.leaf 1261884644) (.leaf 1239004499)) (.branch 74 (.leaf 1216618632) (.leaf 1194713319))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1173275322) (.branch 77 (.leaf 1152291868) (.leaf 1131750631))) (.branch 80 (.branch 79 (.leaf 1111639712) (.leaf 1091947620)) (.branch 81 (.leaf 1072663261) (.leaf 1053775914)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1035275222) (.leaf 1017151175)) (.branch 85 (.leaf 999394094) (.leaf 981994622))) (.branch 88 (.branch 87 (.leaf 964943707) (.leaf 948232593)) (.branch 89 (.leaf 931852807) (.leaf 915796147)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 900054674) (.branch 92 (.leaf 884620699) (.leaf 869486776))) (.branch 95 (.branch 94 (.leaf 854645689) (.leaf 840090447)) (.branch 96 (.leaf 825814274) (.leaf 811810600)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 798073054) (.leaf 784595458)) (.branch 100 (.leaf 771371818) (.leaf 758396316))) (.branch 103 (.branch 102 (.leaf 745663306) (.leaf 733167308)) (.branch 104 (.leaf 720903000) (.leaf 708865213))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 697048926) (.leaf 685449260)) (.branch 108 (.leaf 674061473) (.leaf 662880957))) (.branch 111 (.branch 110 (.leaf 651903230) (.leaf 641123935)) (.branch 112 (.leaf 630538832) (.leaf 620143798)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 609934821) (.leaf 599907995)) (.branch 116 (.leaf 590059517) (.leaf 580385688))) (.branch 119 (.branch 118 (.leaf 570882901) (.leaf 561547645)) (.branch 120 (.leaf 552376501) (.leaf 543366135)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 790).prefactor = (1180399607105649/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 790).cutoff/(generalMeanRows 790).c)).2 =
    (35837852186353/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 790).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 790).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 790).q*(generalMeanRows 790).c/2-2 = (309/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable256.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 790).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 790

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 790).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 790).criticalRate j.val*(generalMeanRows 790).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 790).c*(generalMeanRows 790).criticalPoint j.val)).2-
      (generalMeanRows 790).J/2-(generalMeanRows 790).error (generalMeanGrid j.val)+
      (generalMeanRows 790).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 790).c)).2-
      (generalMeanRows 790).J/2-(generalMeanRows 790).error 4 := by
  have he : (generalMeanRows 790).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 790) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 790)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0790

/-! Kernel-checked entropy margins for general spectral rectangle 791. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0791
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6058784063) (.branch 2 (.leaf 5876011554) (.leaf 5700855607))) (.branch 5 (.branch 4 (.leaf 5532900388) (.leaf 5371758897)) (.branch 6 (.leaf 5217070429) (.leaf 5068498314)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4925727910) (.leaf 4788464792)) (.branch 10 (.leaf 4656433137) (.leaf 4529374260))) (.branch 13 (.branch 12 (.leaf 4407045307) (.leaf 4289218055)) (.branch 14 (.leaf 4175677835) (.leaf 4066222551))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3960661781) (.branch 17 (.leaf 3858815964) (.leaf 3760515648))) (.branch 20 (.branch 19 (.leaf 3665600810) (.leaf 3573920224)) (.branch 21 (.leaf 3485330882) (.leaf 3399697467)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3316891856) (.leaf 3236792669)) (.branch 25 (.leaf 3159284849) (.leaf 3084259276))) (.branch 28 (.branch 27 (.leaf 3011612402) (.leaf 2941245924)) (.branch 29 (.leaf 2873066464) (.leaf 2806985287)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2742918031) (.branch 32 (.leaf 2680784452) (.leaf 2620508193))) (.branch 35 (.branch 34 (.leaf 2562016566) (.leaf 2505240344)) (.branch 36 (.leaf 2450113573) (.leaf 2396573391)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2344559862) (.leaf 2294015816)) (.branch 40 (.leaf 2244886702) (.leaf 2197120452))) (.branch 43 (.branch 42 (.leaf 2150667348) (.leaf 2105479897)) (.branch 44 (.leaf 2061512724) (.leaf 2018722453))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1977067615) (.branch 47 (.leaf 1936508541) (.leaf 1897007283))) (.branch 50 (.branch 49 (.leaf 1858527517) (.leaf 1821034470)) (.branch 51 (.leaf 1784494841) (.leaf 1748876728)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1714149561) (.leaf 1680284038)) (.branch 55 (.leaf 1647252062) (.leaf 1615026685))) (.branch 58 (.branch 57 (.leaf 1583582055) (.leaf 1552893360)) (.branch 59 (.leaf 1522936782) (.leaf 1493689452))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1465129401) (.branch 62 (.leaf 1437235524) (.leaf 1409987536))) (.branch 65 (.branch 64 (.leaf 1383365938) (.leaf 1357351978)) (.branch 66 (.leaf 1331927621) (.leaf 1307075513)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1282778953) (.leaf 1259021863)) (.branch 70 (.leaf 1235788761) (.leaf 1213064735))) (.branch 73 (.branch 72 (.leaf 1190835418) (.leaf 1169086962)) (.branch 74 (.leaf 1147806019) (.leaf 1126979719))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1106595647) (.branch 77 (.leaf 1086641825) (.leaf 1067106696))) (.branch 80 (.branch 79 (.leaf 1047979101) (.leaf 1029248267)) (.branch 81 (.leaf 1010903790) (.leaf 992935618)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 975334037) (.leaf 958089658)) (.branch 85 (.leaf 941193405) (.leaf 924636498))) (.branch 88 (.branch 87 (.leaf 908410447) (.leaf 892507033)) (.branch 89 (.leaf 876918306) (.leaf 861636567)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 846654362) (.branch 92 (.leaf 831964470) (.leaf 817559896))) (.branch 95 (.branch 94 (.leaf 803433862) (.leaf 789579797)) (.branch 96 (.leaf 775991332) (.leaf 762662288)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 749586674) (.leaf 736758676)) (.branch 100 (.leaf 724172650) (.leaf 711823121))) (.branch 103 (.branch 102 (.leaf 699704771) (.leaf 687812436)) (.branch 104 (.leaf 676141098) (.leaf 664685884))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 653442058) (.leaf 642405014)) (.branch 108 (.leaf 631570278) (.leaf 620933495))) (.branch 111 (.branch 110 (.leaf 610490432) (.leaf 600236968)) (.branch 112 (.leaf 590169095) (.leaf 580282912)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 570574620) (.leaf 561040521)) (.branch 116 (.leaf 551677014) (.leaf 542480589))) (.branch 119 (.branch 118 (.leaf 533447828) (.leaf 524575400)) (.branch 120 (.leaf 515860059) (.leaf 507298639)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 791).prefactor = (2305093530094121/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 791).cutoff/(generalMeanRows 791).c)).2 =
    (92987649852269/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 791).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 791).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 791).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 791

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 791).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 791).criticalRate j.val*(generalMeanRows 791).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 791).c*(generalMeanRows 791).criticalPoint j.val)).2-
      (generalMeanRows 791).J/2-(generalMeanRows 791).error (generalMeanGrid j.val)+
      (generalMeanRows 791).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 791).c)).2-
      (generalMeanRows 791).J/2-(generalMeanRows 791).error 4 := by
  have he : (generalMeanRows 791).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 791) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 791)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0791

/-! Kernel-checked entropy margins for general spectral rectangle 792. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0792
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5782129087) (.branch 2 (.leaf 5601434284) (.leaf 5428355760))) (.branch 5 (.branch 4 (.leaf 5262476339) (.leaf 5103407792)) (.branch 6 (.leaf 4950788295) (.leaf 4804280166)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4663567843) (.leaf 4528356075)) (.branch 10 (.leaf 4398368300) (.leaf 4273345176))) (.branch 13 (.branch 12 (.leaf 4153043262) (.leaf 4037233821)) (.branch 14 (.leaf 3925701731) (.leaf 3818244502))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3714671376) (.branch 17 (.leaf 3614802498) (.leaf 3518468174))) (.branch 20 (.branch 19 (.leaf 3425508177) (.leaf 3335771113)) (.branch 21 (.leaf 3249113844) (.leaf 3165400948)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3084504229) (.leaf 3006302255)) (.branch 25 (.leaf 2930679943) (.leaf 2857528163))) (.branch 28 (.branch 27 (.leaf 2786743377) (.leaf 2718227304)) (.branch 29 (.leaf 2651886605) (.leaf 2587632595)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2525380969) (.branch 32 (.leaf 2465051552) (.leaf 2406568061))) (.branch 35 (.branch 34 (.leaf 2349857890) (.leaf 2294851898)) (.branch 36 (.leaf 2241484220) (.leaf 2189692089)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2139415661) (.leaf 2090597865)) (.branch 40 (.leaf 2043184248) (.leaf 1997122838))) (.branch 43 (.branch 42 (.leaf 1952364014) (.leaf 1908860384)) (.branch 44 (.leaf 1866566665) (.leaf 1825439577))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1785437742) (.branch 47 (.leaf 1746521583) (.leaf 1708653240))) (.branch 50 (.branch 49 (.leaf 1671796474) (.leaf 1635916597)) (.branch 51 (.leaf 1600980387) (.leaf 1566956019)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1533813000) (.leaf 1501522097)) (.branch 55 (.leaf 1470055284) (.leaf 1439385679))) (.branch 58 (.branch 57 (.leaf 1409487491) (.leaf 1380335969)) (.branch 59 (.leaf 1351907352) (.leaf 1324178824))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1297128469) (.branch 62 (.leaf 1270735229) (.leaf 1244978865))) (.branch 65 (.branch 64 (.leaf 1219839921) (.leaf 1195299686)) (.branch 66 (.leaf 1171340162) (.leaf 1147944032)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1125094627) (.leaf 1102775901)) (.branch 70 (.leaf 1080972401) (.leaf 1059669242))) (.branch 73 (.branch 72 (.leaf 1038852081) (.leaf 1018507095)) (.branch 74 (.leaf 998620957) (.leaf 979180817))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 960174279) (.branch 77 (.leaf 941589382) (.leaf 923414584))) (.branch 80 (.branch 79 (.leaf 905638742) (.leaf 888251096)) (.branch 81 (.leaf 871241255) (.leaf 854599178)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 838315163) (.leaf 822379830)) (.branch 85 (.leaf 806784112) (.leaf 791519239))) (.branch 88 (.branch 87 (.leaf 776576727) (.leaf 761948369)) (.branch 89 (.leaf 747626219) (.leaf 733602586)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 719870023) (.branch 92 (.leaf 706421316) (.leaf 693249478))) (.branch 95 (.branch 94 (.leaf 680347735) (.leaf 667709525)) (.branch 96 (.leaf 655328484) (.leaf 643198442)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 631313413) (.leaf 619667590)) (.branch 100 (.leaf 608255339) (.leaf 597071190))) (.branch 103 (.branch 102 (.leaf 586109835) (.leaf 575366117)) (.branch 104 (.leaf 564835029) (.leaf 554511706))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 544391422) (.leaf 534469581)) (.branch 108 (.leaf 524741720) (.leaf 515203496))) (.branch 111 (.branch 110 (.leaf 505850686) (.leaf 496679184)) (.branch 112 (.leaf 487684994) (.leaf 478864228)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 470213103) (.leaf 461727935)) (.branch 116 (.leaf 453405137) (.leaf 445241218))) (.branch 119 (.branch 118 (.leaf 437232776) (.leaf 429376498)) (.branch 120 (.leaf 421669155) (.leaf 414107602)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 792).prefactor = (925637711900697/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 792).cutoff/(generalMeanRows 792).c)).2 =
    (180899113972529/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 792).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 792).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 792).q*(generalMeanRows 792).c/2-2 = (1101/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable185.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 792).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 792

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 792).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 792).criticalRate j.val*(generalMeanRows 792).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 792).c*(generalMeanRows 792).criticalPoint j.val)).2-
      (generalMeanRows 792).J/2-(generalMeanRows 792).error (generalMeanGrid j.val)+
      (generalMeanRows 792).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 792).c)).2-
      (generalMeanRows 792).J/2-(generalMeanRows 792).error 4 := by
  have he : (generalMeanRows 792).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 792) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 792)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0792

/-! Kernel-checked entropy margins for general spectral rectangle 793. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0793
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5339465281) (.branch 2 (.leaf 5162231145) (.leaf 4992613887))) (.branch 5 (.branch 4 (.leaf 4830195218) (.leaf 4674585844)) (.branch 6 (.leaf 4525422934) (.leaf 4382367853)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4245104140) (.leaf 4113335701)) (.branch 10 (.leaf 3986785180) (.leaf 3865192490))) (.branch 13 (.branch 12 (.leaf 3748313496) (.leaf 3635918808)) (.branch 14 (.leaf 3527792697) (.leaf 3423732103))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3323545735) (.branch 17 (.leaf 3227053243) (.leaf 3134084467))) (.branch 20 (.branch 19 (.leaf 3044478747) (.leaf 2958084281)) (.branch 21 (.leaf 2874757552) (.leaf 2794362781)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2716771438) (.leaf 2641861779)) (.branch 25 (.leaf 2569518425) (.leaf 2499631969))) (.branch 28 (.branch 27 (.leaf 2432098612) (.leaf 2366819827)) (.branch 29 (.leaf 2303702043) (.leaf 2242656353)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2183598245) (.branch 32 (.leaf 2126447346) (.leaf 2071127185))) (.branch 35 (.branch 34 (.leaf 2017564977) (.leaf 1965691410)) (.branch 36 (.leaf 1915440458) (.leaf 1866749196)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1819557634) (.leaf 1773808557)) (.branch 40 (.leaf 1729447375) (.leaf 1686421986))) (.branch 43 (.branch 42 (.leaf 1644682643) (.leaf 1604181831)) (.branch 44 (.leaf 1564874152) (.leaf 1526716213))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1489666529) (.branch 47 (.leaf 1453685418) (.leaf 1418734919))) (.branch 50 (.branch 49 (.leaf 1384778698) (.leaf 1351781971)) (.branch 51 (.leaf 1319711430) (.leaf 1288535162)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1258222590) (.leaf 1228744403)) (.branch 55 (.leaf 1200072498) (.leaf 1172179918))) (.branch 58 (.branch 57 (.leaf 1145040804) (.leaf 1118630337)) (.branch 59 (.leaf 1092924692) (.leaf 1067900991))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1043537260) (.branch 62 (.leaf 1019812387) (.leaf 996706080))) (.branch 65 (.branch 64 (.leaf 974198835) (.leaf 952271893)) (.branch 66 (.leaf 930907215) (.leaf 910087442)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 889795870) (.leaf 870016418)) (.branch 70 (.leaf 850733602) (.leaf 831932508))) (.branch 73 (.branch 72 (.leaf 813598770) (.leaf 795718542)) (.branch 74 (.leaf 778278479) (.leaf 761265713))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 744667835) (.branch 77 (.leaf 728472877) (.leaf 712669287))) (.branch 80 (.branch 79 (.leaf 697245919) (.leaf 682192012)) (.branch 81 (.leaf 667497176) (.leaf 653151375)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 639144915) (.leaf 625468427)) (.branch 85 (.leaf 612112856) (.leaf 599069450))) (.branch 88 (.branch 87 (.leaf 586329743) (.leaf 573885550)) (.branch 89 (.leaf 561728948) (.leaf 549852276)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 538248116) (.branch 92 (.leaf 526909286) (.leaf 515828834))) (.branch 95 (.branch 94 (.leaf 505000026) (.leaf 494416339)) (.branch 96 (.leaf 484071452) (.leaf 473959241)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 464073767) (.leaf 454409275)) (.branch 100 (.leaf 444960183) (.leaf 435721076))) (.branch 103 (.branch 102 (.leaf 426686702) (.leaf 417851966)) (.branch 104 (.leaf 409211921) (.leaf 400761767))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 392496842) (.leaf 384412622)) (.branch 108 (.leaf 376504710) (.leaf 368768837))) (.branch 111 (.branch 110 (.leaf 361200853) (.leaf 353796729)) (.branch 112 (.leaf 346552546) (.leaf 339464495)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332528874) (.leaf 325742082)) (.branch 116 (.leaf 319100617) (.leaf 312601073))) (.branch 119 (.branch 118 (.leaf 306240136) (.leaf 300014581)) (.branch 120 (.leaf 293921271) (.leaf 287957150)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 793).prefactor = (4637799923163123/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 793).cutoff/(generalMeanRows 793).c)).2 =
    (67586149307683/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 793).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 793).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 793).q*(generalMeanRows 793).c/2-2 = (313/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable173.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 793).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 793

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 793).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 793).criticalRate j.val*(generalMeanRows 793).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 793).c*(generalMeanRows 793).criticalPoint j.val)).2-
      (generalMeanRows 793).J/2-(generalMeanRows 793).error (generalMeanGrid j.val)+
      (generalMeanRows 793).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 793).c)).2-
      (generalMeanRows 793).J/2-(generalMeanRows 793).error 4 := by
  have he : (generalMeanRows 793).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 793) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 793)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0793

/-! Kernel-checked entropy margins for general spectral rectangle 794. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0794
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5309255077) (.branch 2 (.leaf 5140608035) (.leaf 4979196680))) (.branch 5 (.branch 4 (.leaf 4824617367) (.leaf 4676494718)) (.branch 6 (.leaf 4534479148) (.leaf 4398244663)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4267486885) (.leaf 4141921291)) (.branch 10 (.leaf 4021281616) (.leaf 3905318425))) (.branch 13 (.branch 12 (.leaf 3793797816) (.leaf 3686500249)) (.branch 14 (.leaf 3583219476) (.leaf 3483761575))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3387944064) (.branch 17 (.leaf 3295595094) (.leaf 3206552711))) (.branch 20 (.branch 19 (.leaf 3120664174) (.leaf 3037785340)) (.branch 21 (.leaf 2957780085) (.leaf 2880519779)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2805882802) (.leaf 2733754093)) (.branch 25 (.leaf 2664024734) (.leaf 2596591568))) (.branch 28 (.branch 27 (.leaf 2531356839) (.leaf 2468227867)) (.branch 29 (.leaf 2407116735) (.leaf 2347940006)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2290618460) (.branch 32 (.leaf 2235076840) (.leaf 2181243625))) (.branch 35 (.branch 34 (.leaf 2129050817) (.leaf 2078433733)) (.branch 36 (.leaf 2029330824) (.leaf 1981683494)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1935435937) (.leaf 1890534985)) (.branch 40 (.leaf 1846929958) (.leaf 1804572535))) (.branch 43 (.branch 42 (.leaf 1763416621) (.leaf 1723418232)) (.branch 44 (.leaf 1684535381) (.leaf 1646727970))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1609957695) (.branch 47 (.leaf 1574187951) (.leaf 1539383742))) (.branch 50 (.branch 49 (.leaf 1505511603) (.leaf 1472539517)) (.branch 51 (.leaf 1440436843) (.leaf 1409174250)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1378723646) (.leaf 1349058120)) (.branch 55 (.leaf 1320151884) (.leaf 1291980216))) (.branch 58 (.branch 57 (.leaf 1264519406) (.leaf 1237746714)) (.branch 59 (.leaf 1211640315) (.leaf 1186179261))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1161343437) (.branch 62 (.leaf 1137113522) (.leaf 1113470951))) (.branch 65 (.branch 64 (.leaf 1090397880) (.leaf 1067877153)) (.branch 66 (.leaf 1045892270) (.leaf 1024427358)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1003467139) (.leaf 982996907)) (.branch 70 (.leaf 963002501) (.leaf 943470278))) (.branch 73 (.branch 72 (.leaf 924387095) (.leaf 905740282)) (.branch 74 (.leaf 887517624) (.leaf 869707341))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 852298067) (.branch 77 (.leaf 835278836) (.leaf 818639061))) (.branch 80 (.branch 79 (.leaf 802368520) (.leaf 786457339)) (.branch 81 (.leaf 770895982) (.leaf 755675228)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 740786168) (.leaf 726220185)) (.branch 85 (.leaf 711968946) (.leaf 698024388))) (.branch 88 (.branch 87 (.leaf 684378707) (.leaf 671024352)) (.branch 89 (.leaf 657954008) (.leaf 645160592)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 632637244) (.branch 92 (.leaf 620377313) (.leaf 608374354))) (.branch 95 (.branch 94 (.leaf 596622120) (.leaf 585114551)) (.branch 96 (.leaf 573845769) (.leaf 562810071)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 552001925) (.leaf 541415957)) (.branch 100 (.leaf 531046951) (.leaf 520889844))) (.branch 103 (.branch 102 (.leaf 510939715) (.leaf 501191783)) (.branch 104 (.leaf 491641403) (.leaf 482284060))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 473115364) (.leaf 464131047)) (.branch 108 (.leaf 455326955) (.leaf 446699051))) (.branch 111 (.branch 110 (.leaf 438243404) (.leaf 429956189)) (.branch 112 (.leaf 421833685) (.leaf 413872265)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 406068400) (.leaf 398418654)) (.branch 116 (.leaf 390919677) (.leaf 383568207))) (.branch 119 (.branch 118 (.leaf 376361066) (.leaf 369295153)) (.branch 120 (.leaf 362367450) (.leaf 355575012)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 794).prefactor = (4497028991981241/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 794).cutoff/(generalMeanRows 794).c)).2 =
    (38068427937783/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 794).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 794).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 794).q*(generalMeanRows 794).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    have hcontinuation : (generalMeanRows 794).q*(generalMeanRows 794).cutoff/2-2 = (961/483:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable257.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 794).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 794

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 794).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 794).criticalRate j.val*(generalMeanRows 794).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 794).c*(generalMeanRows 794).criticalPoint j.val)).2-
      (generalMeanRows 794).J/2-(generalMeanRows 794).error (generalMeanGrid j.val)+
      (generalMeanRows 794).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 794).c)).2-
      (generalMeanRows 794).J/2-(generalMeanRows 794).error 4 := by
  have he : (generalMeanRows 794).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 794) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 794)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0794

/-! Kernel-checked entropy margins for general spectral rectangle 795. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0795
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5010032690) (.branch 2 (.leaf 4838371678) (.leaf 4674244776))) (.branch 5 (.branch 4 (.leaf 4517232592) (.leaf 4366944968)) (.branch 6 (.leaf 4223018425) (.leaf 4085113889)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3952914657) (.leaf 3826124568)) (.branch 10 (.leaf 3704466368) (.leaf 3587680225))) (.branch 13 (.branch 12 (.leaf 3475522395) (.leaf 3367764007)) (.branch 14 (.leaf 3264189968) (.leaf 3164597954))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3068797505) (.branch 17 (.leaf 2976609183) (.leaf 2887863816))) (.branch 20 (.branch 19 (.leaf 2802401791) (.leaf 2720072417)) (.branch 21 (.leaf 2640733329) (.leaf 2564249947)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2490494970) (.leaf 2419347916)) (.branch 25 (.leaf 2350694691) (.leaf 2284427188))) (.branch 28 (.branch 27 (.leaf 2220442926) (.leaf 2158644701)) (.branch 29 (.leaf 2098940272) (.leaf 2041242067)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1985466902) (.branch 32 (.leaf 1931535732) (.leaf 1879373405))) (.branch 35 (.branch 34 (.leaf 1828908446) (.leaf 1780072842)) (.branch 36 (.leaf 1732801852) (.leaf 1687033823)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1642710019) (.leaf 1599774459)) (.branch 40 (.leaf 1558173774) (.leaf 1517857057))) (.branch 43 (.branch 42 (.leaf 1478775740) (.leaf 1440883464)) (.branch 44 (.leaf 1404135963) (.leaf 1368490958))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1333908050) (.branch 47 (.leaf 1300348627) (.leaf 1267775768))) (.branch 50 (.branch 49 (.leaf 1236154159) (.leaf 1205450015)) (.branch 51 (.leaf 1175630996) (.leaf 1146666142)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1118525803) (.leaf 1091181571)) (.branch 55 (.leaf 1064606224) (.leaf 1038773665))) (.branch 58 (.branch 57 (.leaf 1013658870) (.leaf 989237836)) (.branch 59 (.leaf 965487530) (.leaf 942385848))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 919911566) (.branch 62 (.leaf 898044303) (.leaf 876764480))) (.branch 65 (.branch 64 (.leaf 856053283) (.leaf 835892626)) (.branch 66 (.leaf 816265124) (.leaf 797154053)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 778543327) (.leaf 760417465)) (.branch 70 (.leaf 742761567) (.leaf 725561286))) (.branch 73 (.branch 72 (.leaf 708802807) (.leaf 692472819)) (.branch 74 (.leaf 676558496) (.leaf 661047477))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 645927844) (.branch 77 (.leaf 631188105) (.leaf 616817172))) (.branch 80 (.branch 79 (.leaf 602804350) (.leaf 589139315)) (.branch 81 (.leaf 575812103) (.leaf 562813092)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 550132988) (.leaf 537762814)) (.branch 85 (.leaf 525693895) (.leaf 513917847))) (.branch 88 (.branch 87 (.leaf 502426566) (.leaf 491212212)) (.branch 89 (.leaf 480267207) (.leaf 469584218)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 459156147) (.branch 92 (.leaf 448976128) (.leaf 439037513))) (.branch 95 (.branch 94 (.leaf 429333865) (.leaf 419858949)) (.branch 96 (.leaf 410606727) (.leaf 401571348)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 392747142) (.leaf 384128613)) (.branch 100 (.leaf 375710433) (.leaf 367487436))) (.branch 103 (.branch 102 (.leaf 359454611) (.leaf 351607099)) (.branch 104 (.leaf 343940183) (.leaf 336449287))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 329129970) (.leaf 321977920)) (.branch 108 (.leaf 314988951) (.leaf 308158997))) (.branch 111 (.branch 110 (.leaf 301484110) (.leaf 294960455)) (.branch 112 (.leaf 288584305) (.leaf 282352037)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 276260133) (.leaf 270305170)) (.branch 116 (.leaf 264483823) (.leaf 258792856))) (.branch 119 (.branch 118 (.leaf 253229125) (.leaf 247789568)) (.branch 120 (.leaf 242471211) (.leaf 237271156)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 795).prefactor = (4627804855097353/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 795).cutoff/(generalMeanRows 795).c)).2 =
    (68421473219313/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 795).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 795).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 795).q*(generalMeanRows 795).c/2-2 = (6659/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable215.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 795).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 795

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 795).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 795).criticalRate j.val*(generalMeanRows 795).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 795).c*(generalMeanRows 795).criticalPoint j.val)).2-
      (generalMeanRows 795).J/2-(generalMeanRows 795).error (generalMeanGrid j.val)+
      (generalMeanRows 795).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 795).c)).2-
      (generalMeanRows 795).J/2-(generalMeanRows 795).error 4 := by
  have he : (generalMeanRows 795).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 795) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 795)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0795

/-! Kernel-checked entropy margins for general spectral rectangle 796. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0796
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5138802373) (.branch 2 (.leaf 4970648088) (.leaf 4809812061))) (.branch 5 (.branch 4 (.leaf 4655883339) (.leaf 4508479823)) (.branch 6 (.leaf 4367245745) (.leaf 4231849419)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4101981229) (.leaf 3977351828)) (.branch 10 (.leaf 3857690512) (.leaf 3742743759))) (.branch 13 (.branch 12 (.leaf 3632273904) (.leaf 3526057940)) (.branch 14 (.leaf 3423886430) (.leaf 3325562514))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3230901006) (.branch 17 (.leaf 3139727568) (.leaf 3051877954))) (.branch 20 (.branch 19 (.leaf 2967197315) (.leaf 2885539565)) (.branch 21 (.leaf 2806766795) (.leaf 2730748733)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2657362246) (.leaf 2586490883)) (.branch 25 (.leaf 2518024449) (.leaf 2451858611))) (.branch 28 (.branch 27 (.leaf 2387894535) (.leaf 2326038547)) (.branch 29 (.leaf 2266201820) (.leaf 2208300080)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2152253338) (.branch 32 (.leaf 2097985633) (.leaf 2045424797))) (.branch 35 (.branch 34 (.leaf 1994502238) (.leaf 1945152732)) (.branch 36 (.leaf 1897314229) (.leaf 1850927678)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1805936855) (.leaf 1762288209)) (.branch 40 (.leaf 1719930713) (.leaf 1678815724))) (.branch 43 (.branch 42 (.leaf 1638896856) (.leaf 1600129860)) (.branch 44 (.leaf 1562472502) (.leaf 1525884466))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1490327245) (.branch 47 (.leaf 1455764050) (.leaf 1422159719))) (.branch 50 (.branch 49 (.leaf 1389480634) (.leaf 1357694640)) (.branch 51 (.leaf 1326770973) (.leaf 1296680188)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1267394091) (.leaf 1238885681)) (.branch 55 (.leaf 1211129084) (.leaf 1184099505))) (.branch 58 (.branch 57 (.leaf 1157773169) (.leaf 1132127275)) (.branch 59 (.leaf 1107139945) (.leaf 1082790186))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1059057841) (.branch 62 (.leaf 1035923551) (.leaf 1013368721))) (.branch 65 (.branch 64 (.leaf 991375480) (.leaf 969926648)) (.branch 66 (.leaf 949005707) (.leaf 928596766)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 908684535) (.leaf 889254298)) (.branch 70 (.leaf 870291885) (.leaf 851783651))) (.branch 73 (.branch 72 (.leaf 833716447) (.leaf 816077605)) (.branch 74 (.leaf 798854911) (.leaf 782036587))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 765611274) (.branch 77 (.leaf 749568011) (.leaf 733896220))) (.branch 80 (.branch 79 (.leaf 718585690) (.leaf 703626557)) (.branch 81 (.leaf 689009295) (.leaf 674724701)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 660763879) (.leaf 647118227)) (.branch 85 (.leaf 633779429) (.leaf 620739440))) (.branch 88 (.branch 87 (.leaf 607990477) (.leaf 595525006)) (.branch 89 (.leaf 583335735) (.leaf 571415601)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 559757767) (.branch 92 (.leaf 548355605) (.leaf 537202696))) (.branch 95 (.branch 94 (.leaf 526292815) (.leaf 515619928)) (.branch 96 (.leaf 505178185) (.leaf 494961909)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 484965595) (.leaf 475183899)) (.branch 100 (.leaf 465611633) (.leaf 456243763))) (.branch 103 (.branch 102 (.leaf 447075399) (.leaf 438101792)) (.branch 104 (.leaf 429318326) (.leaf 420720520))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 412304017) (.leaf 404064579)) (.branch 108 (.leaf 395998091) (.leaf 388100545))) (.branch 111 (.branch 110 (.leaf 380368049) (.leaf 372796811)) (.branch 112 (.leaf 365383146) (.leaf 358123465)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 351014275) (.leaf 344052176)) (.branch 116 (.leaf 337233857) (.leaf 330556095))) (.branch 119 (.branch 118 (.leaf 324015749) (.leaf 317609758)) (.branch 120 (.leaf 311335144) (.leaf 305189001)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 796).prefactor = (1138282550979981/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 796).cutoff/(generalMeanRows 796).c)).2 =
    (188343849846671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 796).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 796).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 796).q*(generalMeanRows 796).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 796).q*(generalMeanRows 796).cutoff/2-2 = (3886/1911:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable258.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 796).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 796

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 796).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 796).criticalRate j.val*(generalMeanRows 796).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 796).c*(generalMeanRows 796).criticalPoint j.val)).2-
      (generalMeanRows 796).J/2-(generalMeanRows 796).error (generalMeanGrid j.val)+
      (generalMeanRows 796).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 796).c)).2-
      (generalMeanRows 796).J/2-(generalMeanRows 796).error 4 := by
  have he : (generalMeanRows 796).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 796) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 796)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0796

/-! Kernel-checked entropy margins for general spectral rectangle 797. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0797
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5216557005) (.branch 2 (.leaf 5046082286) (.leaf 4882972916))) (.branch 5 (.branch 4 (.leaf 4726818778) (.leaf 4577238422)) (.branch 6 (.leaf 4433876555) (.leaf 4296401808)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4164504739) (.leaf 4037896040)) (.branch 10 (.leaf 3916304927) (.leaf 3799477688))) (.branch 13 (.branch 12 (.leaf 3687176370) (.leaf 3579177591)) (.branch 14 (.leaf 3475271455) (.leaf 3375260575))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3278959175) (.branch 17 (.leaf 3186192270) (.leaf 3096794919))) (.branch 20 (.branch 19 (.leaf 3010611535) (.leaf 2927495259)) (.branch 21 (.leaf 2847307374) (.leaf 2769916778)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2695199482) (.leaf 2623038165)) (.branch 25 (.leaf 2553321744) (.leaf 2485944993))) (.branch 28 (.branch 27 (.leaf 2420808172) (.leaf 2357816700)) (.branch 29 (.leaf 2296880841) (.leaf 2237915413)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2180839519) (.branch 32 (.leaf 2125576297) (.leaf 2072052685))) (.branch 35 (.branch 34 (.leaf 2020199202) (.leaf 1969949747)) (.branch 36 (.leaf 1921241403) (.leaf 1874014264)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1828211261) (.leaf 1783778015)) (.branch 40 (.leaf 1740662682) (.leaf 1698815819))) (.branch 43 (.branch 42 (.leaf 1658190255) (.leaf 1618740968)) (.branch 44 (.leaf 1580424973) (.leaf 1543201215))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1507030466) (.branch 47 (.leaf 1471875232) (.leaf 1437699663))) (.branch 50 (.branch 49 (.leaf 1404469470) (.leaf 1372151844)) (.branch 51 (.leaf 1340715383) (.leaf 1310130020)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1280366958) (.leaf 1251398606)) (.branch 55 (.leaf 1223198521) (.leaf 1195741350))) (.branch 58 (.branch 57 (.leaf 1169002779) (.leaf 1142959482)) (.branch 59 (.leaf 1117589073) (.leaf 1092870063))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1068781816) (.branch 62 (.leaf 1045304511) (.leaf 1022419101))) (.branch 65 (.branch 64 (.leaf 1000107279) (.leaf 978351442)) (.branch 66 (.leaf 957134662) (.leaf 936440653)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 916253742) (.leaf 896558840)) (.branch 70 (.leaf 877341420) (.leaf 858587488))) (.branch 73 (.branch 72 (.leaf 840283561) (.leaf 822416646)) (.branch 74 (.leaf 804974214) (.leaf 787944187))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 771314911) (.branch 77 (.leaf 755075144) (.leaf 739214034))) (.branch 80 (.branch 79 (.leaf 723721106) (.leaf 708586244)) (.branch 81 (.leaf 693799676) (.leaf 679351960)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 665233973) (.leaf 651436893)) (.branch 85 (.leaf 637952192) (.leaf 624771619))) (.branch 88 (.branch 87 (.leaf 611887192) (.leaf 599291189)) (.branch 89 (.leaf 586976133) (.leaf 574934785)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 563160136) (.branch 92 (.leaf 551645396) (.leaf 540383984))) (.branch 95 (.branch 94 (.leaf 529369526) (.leaf 518595839)) (.branch 96 (.leaf 508056932) (.leaf 497746993)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 487660383) (.leaf 477791634)) (.branch 100 (.leaf 468135436) (.leaf 458686637))) (.branch 103 (.branch 102 (.leaf 449440234) (.leaf 440391370)) (.branch 104 (.leaf 431535326) (.leaf 422867518))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 414383493) (.leaf 406078921)) (.branch 108 (.leaf 397949596) (.leaf 389991425))) (.branch 111 (.branch 110 (.leaf 382200432) (.leaf 374572747)) (.branch 112 (.leaf 367104606) (.leaf 359792346)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 352632406) (.leaf 345621315)) (.branch 116 (.leaf 338755697) (.leaf 332032266))) (.branch 119 (.branch 118 (.leaf 325447819) (.leaf 318999240)) (.branch 120 (.leaf 312683491) (.leaf 306497612)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 797).prefactor = (1141191224772489/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 797).cutoff/(generalMeanRows 797).c)).2 =
    (5714978580643/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 797).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 797).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 797).q*(generalMeanRows 797).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 797).q*(generalMeanRows 797).cutoff/2-2 = (961/483:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable257.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 797).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 797

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 797).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 797).criticalRate j.val*(generalMeanRows 797).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 797).c*(generalMeanRows 797).criticalPoint j.val)).2-
      (generalMeanRows 797).J/2-(generalMeanRows 797).error (generalMeanGrid j.val)+
      (generalMeanRows 797).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 797).c)).2-
      (generalMeanRows 797).J/2-(generalMeanRows 797).error 4 := by
  have he : (generalMeanRows 797).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 797) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 797)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0797

/-! Kernel-checked entropy margins for general spectral rectangle 798. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0798
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5311510894) (.branch 2 (.leaf 5145124685) (.leaf 4985886874))) (.branch 5 (.branch 4 (.leaf 4833395505) (.leaf 4687276915)) (.branch 6 (.leaf 4547183261) (.leaf 4412790315)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4283795484) (.leaf 4159916047)) (.branch 10 (.leaf 4040887553) (.leaf 3926462393))) (.branch 13 (.branch 12 (.leaf 3816408496) (.leaf 3710508152)) (.branch 14 (.leaf 3608556946) (.leaf 3510362783))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3415744999) (.branch 17 (.leaf 3324533554) (.leaf 3236568289))) (.branch 20 (.branch 19 (.leaf 3151698243) (.leaf 3069781031)) (.branch 21 (.leaf 2990682271) (.leaf 2914275050)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2840439443) (.leaf 2769062054)) (.branch 25 (.leaf 2700035607) (.leaf 2633258556))) (.branch 28 (.branch 27 (.leaf 2568634731) (.leaf 2506073001)) (.branch 29 (.leaf 2445486971) (.leaf 2386794696)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2329918409) (.branch 32 (.leaf 2274784281) (.leaf 2221322182))) (.branch 35 (.branch 34 (.leaf 2169465470) (.leaf 2119150791)) (.branch 36 (.leaf 2070317885) (.leaf 2022909414)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1976870801) (.leaf 1932150066)) (.branch 40 (.leaf 1888697692) (.leaf 1846466483))) (.branch 43 (.branch 42 (.leaf 1805411441) (.leaf 1765489645)) (.branch 44 (.leaf 1726660139) (.leaf 1688883828))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1652123377) (.branch 47 (.leaf 1616343124) (.leaf 1581508983))) (.branch 50 (.branch 49 (.leaf 1547588373) (.leaf 1514550130)) (.branch 51 (.leaf 1482364442) (.leaf 1451002775)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1420437813) (.leaf 1390643392)) (.branch 55 (.leaf 1361594444) (.leaf 1333266945))) (.branch 58 (.branch 57 (.leaf 1305637860) (.leaf 1278685096)) (.branch 59 (.leaf 1252387457) (.leaf 1226724598))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1201676987) (.branch 62 (.leaf 1177225865) (.leaf 1153353207))) (.branch 65 (.branch 64 (.leaf 1130041691) (.leaf 1107274663)) (.branch 66 (.leaf 1085036105) (.leaf 1063310609)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1042083343) (.leaf 1021340031)) (.branch 70 (.leaf 1001066925) (.leaf 981250780))) (.branch 73 (.branch 72 (.leaf 961878831) (.leaf 942938777)) (.branch 74 (.leaf 924418752) (.leaf 906307313))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 888593419) (.branch 77 (.leaf 871266413) (.leaf 854316004))) (.branch 80 (.branch 79 (.leaf 837732255) (.leaf 821505566)) (.branch 81 (.leaf 805626660) (.leaf 790086568)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 774876618) (.leaf 759988422)) (.branch 85 (.leaf 745413865) (.leaf 731145092))) (.branch 88 (.branch 87 (.leaf 717174500) (.leaf 703494727)) (.branch 89 (.leaf 690098640) (.leaf 676979329)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 664130097) (.branch 92 (.leaf 651544452) (.leaf 639216099))) (.branch 95 (.branch 94 (.leaf 627138931) (.leaf 615307025)) (.branch 96 (.leaf 603714631) (.leaf 592356169)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 581226220) (.leaf 570319523)) (.branch 100 (.leaf 559630965) (.leaf 549155581))) (.branch 103 (.branch 102 (.leaf 538888544) (.leaf 528825160)) (.branch 104 (.leaf 518960869) (.leaf 509291233))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 499811936) (.leaf 490518778)) (.branch 108 (.leaf 481407675) (.leaf 472474647))) (.branch 111 (.branch 110 (.leaf 463715822) (.leaf 455127429)) (.branch 112 (.leaf 446705796) (.leaf 438447345)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 430348589) (.leaf 422406133)) (.branch 116 (.leaf 414616664) (.leaf 406976955))) (.branch 119 (.branch 118 (.leaf 399483859) (.leaf 392134306)) (.branch 120 (.leaf 384925302) (.leaf 377853928)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 798).prefactor = (1122363451522039/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 798).cutoff/(generalMeanRows 798).c)).2 =
    (397291159227731/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 798).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 798).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 798).q*(generalMeanRows 798).c/2-2 = (1427/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable259.value]
    have hcontinuation : (generalMeanRows 798).q*(generalMeanRows 798).cutoff/2-2 = (1921/943:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable260.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 798).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 798

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 798).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 798).criticalRate j.val*(generalMeanRows 798).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 798).c*(generalMeanRows 798).criticalPoint j.val)).2-
      (generalMeanRows 798).J/2-(generalMeanRows 798).error (generalMeanGrid j.val)+
      (generalMeanRows 798).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 798).c)).2-
      (generalMeanRows 798).J/2-(generalMeanRows 798).error 4 := by
  have he : (generalMeanRows 798).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 798) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 798)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0798

/-! Kernel-checked entropy margins for general spectral rectangle 799. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0799
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5271788249) (.branch 2 (.leaf 5104109584) (.leaf 4943703959))) (.branch 5 (.branch 4 (.leaf 4790160387) (.leaf 4643096859)) (.branch 6 (.leaf 4502157814) (.leaf 4367011877)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4237349840) (.leaf 4112882846)) (.branch 10 (.leaf 3993340758) (.leaf 3878470690))) (.branch 13 (.branch 12 (.leaf 3768035669) (.leaf 3661813438)) (.branch 14 (.leaf 3559595354) (.leaf 3461185390))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3366399229) (.branch 17 (.leaf 3275063433) (.leaf 3187014678))) (.branch 20 (.branch 19 (.leaf 3102099059) (.leaf 3020171452)) (.branch 21 (.leaf 2941094919) (.leaf 2864740172)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2790985067) (.leaf 2719714145)) (.branch 25 (.leaf 2650818204) (.leaf 2584193904))) (.branch 28 (.branch 27 (.leaf 2519743400) (.leaf 2457374001)) (.branch 29 (.leaf 2396997857) (.leaf 2338531662)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2281896383) (.branch 32 (.leaf 2227017007) (.leaf 2173822301))) (.branch 35 (.branch 34 (.leaf 2122244593) (.leaf 2072219565)) (.branch 36 (.leaf 2023686060) (.leaf 1976585903)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1930863730) (.leaf 1886466834)) (.branch 40 (.leaf 1843345012) (.leaf 1801450432))) (.branch 43 (.branch 42 (.leaf 1760737500) (.leaf 1721162738)) (.branch 44 (.leaf 1682684670) (.leaf 1645263716))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1608862089) (.branch 47 (.leaf 1573443700) (.leaf 1538974071))) (.branch 50 (.branch 49 (.leaf 1505420248) (.leaf 1472750724)) (.branch 51 (.leaf 1440935364) (.leaf 1409945333)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1379753033) (.leaf 1350332037)) (.branch 55 (.leaf 1321657033) (.leaf 1293703766))) (.branch 58 (.branch 57 (.leaf 1266448989) (.leaf 1239870408)) (.branch 59 (.leaf 1213946642) (.leaf 1188657171))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1163982301) (.branch 62 (.leaf 1139903122) (.leaf 1116401467))) (.branch 65 (.branch 64 (.leaf 1093459884) (.leaf 1071061594)) (.branch 66 (.leaf 1049190468) (.leaf 1027830988)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1006968226) (.leaf 986587813)) (.branch 70 (.leaf 966675914) (.leaf 947219206))) (.branch 73 (.branch 72 (.leaf 928204850) (.leaf 909620475)) (.branch 74 (.leaf 891454153) (.leaf 873694383))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 856330067) (.branch 77 (.leaf 839350498) (.leaf 822745341))) (.branch 80 (.branch 79 (.leaf 806504615) (.leaf 790618679)) (.branch 81 (.leaf 775078222) (.leaf 759874240)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 744998032) (.leaf 730441183)) (.branch 85 (.leaf 716195551) (.leaf 702253260))) (.branch 88 (.branch 87 (.leaf 688606686) (.leaf 675248448)) (.branch 89 (.leaf 662171398) (.leaf 649368610)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 636833375) (.branch 92 (.leaf 624559190) (.leaf 612539750))) (.branch 95 (.branch 94 (.leaf 600768941) (.leaf 589240831)) (.branch 96 (.leaf 577949667) (.leaf 566889864)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 556056000) (.leaf 545442812)) (.branch 100 (.leaf 535045187) (.leaf 524858159))) (.branch 103 (.branch 102 (.leaf 514876903) (.leaf 505096727)) (.branch 104 (.leaf 495513074) (.leaf 486121509))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 476917720) (.leaf 467897515)) (.branch 108 (.leaf 459056812) (.leaf 450391639))) (.branch 111 (.branch 110 (.leaf 441898132) (.leaf 433572527)) (.branch 112 (.leaf 425411159) (.leaf 417410460)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 409566953) (.leaf 401877249)) (.branch 116 (.leaf 394338049) (.leaf 386946134))) (.branch 119 (.branch 118 (.leaf 379698369) (.leaf 372591696)) (.branch 120 (.leaf 365623131) (.leaf 358789768)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 799).prefactor = (4547424013638751/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 799).cutoff/(generalMeanRows 799).c)).2 =
    (39712300572099/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 799).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 799).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 799).q*(generalMeanRows 799).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    have hcontinuation : (generalMeanRows 799).q*(generalMeanRows 799).cutoff/2-2 = (7814/3801:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable261.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 799).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 799

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 799).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 799).criticalRate j.val*(generalMeanRows 799).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 799).c*(generalMeanRows 799).criticalPoint j.val)).2-
      (generalMeanRows 799).J/2-(generalMeanRows 799).error (generalMeanGrid j.val)+
      (generalMeanRows 799).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 799).c)).2-
      (generalMeanRows 799).J/2-(generalMeanRows 799).error 4 := by
  have he : (generalMeanRows 799).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 799) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 799)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0799

/-! Kernel-checked entropy margins for general spectral rectangle 800. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0800
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5222195850) (.branch 2 (.leaf 5053652726) (.leaf 4892445044))) (.branch 5 (.branch 4 (.leaf 4738158730) (.leaf 4590408877)) (.branch 6 (.leaf 4448837200) (.leaf 4313109758)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4182914924) (.leaf 4057961556)) (.branch 10 (.leaf 3937977358) (.leaf 3822707398))) (.branch 13 (.branch 12 (.leaf 3711912769) (.leaf 3605369373)) (.branch 14 (.leaf 3502866823) (.leaf 3404207434))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3309205312) (.branch 17 (.leaf 3217685514) (.leaf 3129483286))) (.branch 20 (.branch 19 (.leaf 3044443359) (.leaf 2962419305)) (.branch 21 (.leaf 2883272943) (.leaf 2806873795)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2733098582) (.leaf 2661830757)) (.branch 25 (.leaf 2592960078) (.leaf 2526382208))) (.branch 28 (.branch 27 (.leaf 2461998347) (.leaf 2399714890)) (.branch 29 (.leaf 2339443108) (.leaf 2281098853)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2224602286) (.branch 32 (.leaf 2169877616) (.leaf 2116852866))) (.branch 35 (.branch 34 (.leaf 2065459649) (.leaf 2015632958)) (.branch 36 (.leaf 1967310976) (.leaf 1920434892)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1874948732) (.leaf 1830799200)) (.branch 40 (.leaf 1787935528) (.leaf 1746309340))) (.branch 43 (.branch 42 (.leaf 1705874517) (.leaf 1666587079)) (.branch 44 (.leaf 1628405064) (.leaf 1591288424))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1555198923) (.branch 47 (.leaf 1520100039) (.leaf 1485956876))) (.branch 50 (.branch 49 (.leaf 1452736078) (.leaf 1420405753)) (.branch 51 (.leaf 1388935391) (.leaf 1358295799)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1328459032) (.leaf 1299398331)) (.branch 55 (.leaf 1271088062) (.leaf 1243503661))) (.branch 58 (.branch 57 (.leaf 1216621584) (.leaf 1190419250)) (.branch 59 (.leaf 1164874999) (.leaf 1139968049))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1115678447) (.branch 62 (.leaf 1091987036) (.leaf 1068875413))) (.branch 65 (.branch 64 (.leaf 1046325895) (.leaf 1024321485)) (.branch 66 (.leaf 1002845840) (.leaf 981883240)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 961418559) (.leaf 941437240)) (.branch 70 (.leaf 921925266) (.leaf 902869138))) (.branch 73 (.branch 72 (.leaf 884255851) (.leaf 866072871)) (.branch 74 (.leaf 848308116) (.leaf 830949934))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 813987085) (.branch 77 (.leaf 797408725) (.leaf 781204385))) (.branch 80 (.branch 79 (.leaf 765363958) (.leaf 749877683)) (.branch 81 (.leaf 734736130) (.leaf 719930184)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 705451037) (.leaf 691290171)) (.branch 85 (.leaf 677439347) (.leaf 663890593))) (.branch 88 (.branch 87 (.leaf 650636196) (.leaf 637668688)) (.branch 89 (.leaf 624980840) (.leaf 612565647)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 600416326) (.branch 92 (.leaf 588526301) (.leaf 576889200))) (.branch 95 (.branch 94 (.leaf 565498843) (.leaf 554349238)) (.branch 96 (.leaf 543434572) (.leaf 532749204)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 522287660) (.leaf 512044627)) (.branch 100 (.leaf 502014945) (.leaf 492193602))) (.branch 103 (.branch 102 (.leaf 482575730) (.leaf 473156599)) (.branch 104 (.leaf 463931612) (.leaf 454896300))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 446046319) (.leaf 437377443)) (.branch 108 (.leaf 428885563) (.leaf 420566680))) (.branch 111 (.branch 110 (.leaf 412416904) (.leaf 404432447)) (.branch 112 (.leaf 396609624) (.leaf 388944845)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 381434616) (.leaf 374075533)) (.branch 116 (.leaf 366864279) (.leaf 359797623))) (.branch 119 (.branch 118 (.leaf 352872418) (.leaf 346085593)) (.branch 120 (.leaf 339434158) (.leaf 332915196)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 800).prefactor = (2289901035184727/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 800).cutoff/(generalMeanRows 800).c)).2 =
    (389632333991831/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 800).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 800).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 800).q*(generalMeanRows 800).c/2-2 = (747/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable220.value]
    have hcontinuation : (generalMeanRows 800).q*(generalMeanRows 800).cutoff/2-2 = (7814/3801:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable261.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 800).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 800

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 800).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 800).criticalRate j.val*(generalMeanRows 800).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 800).c*(generalMeanRows 800).criticalPoint j.val)).2-
      (generalMeanRows 800).J/2-(generalMeanRows 800).error (generalMeanGrid j.val)+
      (generalMeanRows 800).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 800).c)).2-
      (generalMeanRows 800).J/2-(generalMeanRows 800).error 4 := by
  have he : (generalMeanRows 800).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 800) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 800)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0800

/-! Kernel-checked entropy margins for general spectral rectangle 801. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0801
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5176026571) (.branch 2 (.leaf 5006654218) (.leaf 4844653135))) (.branch 5 (.branch 4 (.leaf 4689609392) (.leaf 4541138122)) (.branch 6 (.leaf 4398880980) (.leaf 4262503876)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4131694954) (.leaf 4006162768)) (.branch 10 (.leaf 3885634656) (.leaf 3769855257))) (.branch 13 (.branch 12 (.leaf 3658585186) (.leaf 3551599821)) (.branch 14 (.leaf 3448688206) (.leaf 3349652056))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3254304844) (.branch 17 (.leaf 3162470969) (.leaf 3073984994))) (.branch 20 (.branch 19 (.leaf 2988690949) (.leaf 2906441691)) (.branch 21 (.leaf 2827098311) (.leaf 2750529593)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2676611513) (.leaf 2605226776)) (.branch 25 (.leaf 2536264388) (.leaf 2469619261))) (.branch 28 (.branch 27 (.leaf 2405191845) (.leaf 2342887788)) (.branch 29 (.leaf 2282617618) (.leaf 2224296453)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2167843722) (.branch 32 (.leaf 2113182915) (.leaf 2060241342))) (.branch 35 (.branch 34 (.leaf 2008949913) (.leaf 1959242931)) (.branch 36 (.leaf 1911057898) (.leaf 1864335334)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1819018609) (.leaf 1775053784)) (.branch 40 (.leaf 1732389460) (.leaf 1690976645))) (.branch 43 (.branch 42 (.leaf 1650768615) (.leaf 1611720800)) (.branch 44 (.leaf 1573790662) (.leaf 1536937591))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1501122803) (.branch 47 (.leaf 1466309240) (.leaf 1432461488))) (.branch 50 (.branch 49 (.leaf 1399545684) (.leaf 1367529440)) (.branch 51 (.leaf 1336381770) (.leaf 1306073015)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1276574777) (.leaf 1247859858)) (.branch 55 (.leaf 1219902200) (.leaf 1192676825))) (.branch 58 (.branch 57 (.leaf 1166159788) (.leaf 1140328121)) (.branch 59 (.leaf 1115159790) (.leaf 1090633647))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1066729390) (.branch 62 (.leaf 1043427522) (.leaf 1020709310))) (.branch 65 (.branch 64 (.leaf 998556755) (.leaf 976952554)) (.branch 66 (.leaf 955880066) (.leaf 935323288)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 915266818) (.leaf 895695833)) (.branch 70 (.leaf 876596062) (.leaf 857953758))) (.branch 73 (.branch 72 (.leaf 839755681) (.leaf 821989067)) (.branch 74 (.leaf 804641616) (.leaf 787701464))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 771157170) (.branch 77 (.leaf 754997694) (.leaf 739212381))) (.branch 80 (.branch 79 (.leaf 723790944) (.leaf 708723451)) (.branch 81 (.leaf 694000306) (.leaf 679612238)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 665550287) (.leaf 651805789)) (.branch 85 (.leaf 638370369) (.leaf 625235921))) (.branch 88 (.branch 87 (.leaf 612394608) (.leaf 599838840)) (.branch 89 (.leaf 587561273) (.leaf 575554793)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 563812512) (.branch 92 (.leaf 552327756) (.leaf 541094058))) (.branch 95 (.branch 94 (.leaf 530105148) (.leaf 519354950)) (.branch 96 (.leaf 508837569) (.leaf 498547290)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 488478565) (.leaf 478626012)) (.branch 100 (.leaf 468984407) (.leaf 459548679))) (.branch 103 (.branch 102 (.leaf 450313901) (.leaf 441275291)) (.branch 104 (.leaf 432428201) (.leaf 423768115))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 415290644) (.leaf 406991522)) (.branch 108 (.leaf 398866602) (.leaf 390911848))) (.branch 111 (.branch 110 (.leaf 383123340) (.leaf 375497258)) (.branch 112 (.leaf 368029890) (.leaf 360717621)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 353556934) (.leaf 346544404)) (.branch 116 (.leaf 339676695) (.leaf 332950561))) (.branch 119 (.branch 118 (.leaf 326362837) (.leaf 319910444)) (.branch 120 (.leaf 313590378) (.leaf 307399713)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 801).prefactor = (4586111938975013/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 801).cutoff/(generalMeanRows 801).c)).2 =
    (188343849846671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 801).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 801).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 801).q*(generalMeanRows 801).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    have hcontinuation : (generalMeanRows 801).q*(generalMeanRows 801).cutoff/2-2 = (3886/1911:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable258.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 801).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 801

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 801).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 801).criticalRate j.val*(generalMeanRows 801).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 801).c*(generalMeanRows 801).criticalPoint j.val)).2-
      (generalMeanRows 801).J/2-(generalMeanRows 801).error (generalMeanGrid j.val)+
      (generalMeanRows 801).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 801).c)).2-
      (generalMeanRows 801).J/2-(generalMeanRows 801).error 4 := by
  have he : (generalMeanRows 801).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 801) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 801)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0801

/-! Kernel-checked entropy margins for general spectral rectangle 802. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0802
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5046638722) (.branch 2 (.leaf 4876880482) (.leaf 4714566076))) (.branch 5 (.branch 4 (.leaf 4559278109) (.leaf 4410628436)) (.branch 6 (.leaf 4268255604) (.leaf 4131822578)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4001014698) (.leaf 3875537856)) (.branch 10 (.leaf 3755116851) (.leaf 3639493904))) (.branch 13 (.branch 12 (.leaf 3528427322) (.leaf 3421690277)) (.branch 14 (.leaf 3319069706) (.leaf 3220365308))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3125388625) (.branch 17 (.leaf 3033962206) (.leaf 2945918842))) (.branch 20 (.branch 19 (.leaf 2861100863) (.leaf 2779359493)) (.branch 21 (.leaf 2700554257) (.leaf 2624552434)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2551228553) (.leaf 2480463931)) (.branch 25 (.leaf 2412146236) (.leaf 2346169094))) (.branch 28 (.branch 27 (.leaf 2282431720) (.leaf 2220838570)) (.branch 29 (.leaf 2161299027) (.leaf 2103727106)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2048041174) (.branch 32 (.leaf 1994163698) (.leaf 1942021003))) (.branch 35 (.branch 34 (.leaf 1891543051) (.leaf 1842663230)) (.branch 36 (.leaf 1795318162) (.leaf 1749447519)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1704993855) (.leaf 1661902441)) (.branch 40 (.leaf 1620121123) (.leaf 1579600175))) (.branch 43 (.branch 42 (.leaf 1540292174) (.leaf 1502151868)) (.branch 44 (.leaf 1465136069) (.leaf 1429203538))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1394314884) (.branch 47 (.leaf 1360432468) (.leaf 1327520315))) (.branch 50 (.branch 49 (.leaf 1295544021) (.leaf 1264470680)) (.branch 51 (.leaf 1234268805) (.leaf 1204908257)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1176360175) (.leaf 1148596917)) (.branch 55 (.leaf 1121591996) (.leaf 1095320026))) (.branch 58 (.branch 57 (.leaf 1069756665) (.leaf 1044878568)) (.branch 59 (.leaf 1020663336) (.leaf 997089473))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 974136341) (.branch 62 (.leaf 951784122) (.leaf 930013776))) (.branch 65 (.branch 64 (.leaf 908807009) (.leaf 888146233)) (.branch 66 (.leaf 868014540) (.leaf 848395665)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 829273960) (.leaf 810634365)) (.branch 70 (.leaf 792462384) (.leaf 774744054))) (.branch 73 (.branch 72 (.leaf 757465927) (.leaf 740615046)) (.branch 74 (.leaf 724178923) (.leaf 708145515))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 692503214) (.branch 77 (.leaf 677240817) (.leaf 662347517))) (.branch 80 (.branch 79 (.leaf 647812884) (.leaf 633626847)) (.branch 81 (.leaf 619779682) (.leaf 606261995)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 593064710) (.leaf 580179055)) (.branch 85 (.leaf 567596551) (.leaf 555308999))) (.branch 88 (.branch 87 (.leaf 543308469) (.leaf 531587288)) (.branch 89 (.leaf 520138033) (.leaf 508953518)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 498026786) (.branch 92 (.leaf 487351101) (.leaf 476919937))) (.branch 95 (.branch 94 (.leaf 466726972) (.leaf 456766081)) (.branch 96 (.leaf 447031326) (.leaf 437516950)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 428217371) (.leaf 419127175)) (.branch 100 (.leaf 410241110) (.leaf 401554080))) (.branch 103 (.branch 102 (.leaf 393061139) (.leaf 384757486)) (.branch 104 (.leaf 376638459) (.leaf 368699533))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 360936309) (.leaf 353344519)) (.branch 108 (.leaf 345920011) (.leaf 338658753))) (.branch 111 (.branch 110 (.leaf 331556824) (.leaf 324610414)) (.branch 112 (.leaf 317815816) (.leaf 311169429)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 304667746) (.leaf 298307357)) (.branch 116 (.leaf 292084945) (.leaf 285997281))) (.branch 119 (.branch 118 (.leaf 280041222) (.leaf 274213711)) (.branch 120 (.leaf 268511767) (.leaf 262932493)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 802).prefactor = (1154833146364983/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 802).cutoff/(generalMeanRows 802).c)).2 =
    (7239631046073/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 802).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 802).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 802).q*(generalMeanRows 802).c/2-2 = (1617/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable243.value]
    have hcontinuation : (generalMeanRows 802).q*(generalMeanRows 802).cutoff/2-2 = (3886/1911:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable258.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 802).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 802

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 802).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 802).criticalRate j.val*(generalMeanRows 802).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 802).c*(generalMeanRows 802).criticalPoint j.val)).2-
      (generalMeanRows 802).J/2-(generalMeanRows 802).error (generalMeanGrid j.val)+
      (generalMeanRows 802).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 802).c)).2-
      (generalMeanRows 802).J/2-(generalMeanRows 802).error 4 := by
  have he : (generalMeanRows 802).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 802) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 802)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0802

/-! Kernel-checked entropy margins for general spectral rectangle 803. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0803
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5089423106) (.branch 2 (.leaf 4920447202) (.leaf 4758879063))) (.branch 5 (.branch 4 (.leaf 4604301262) (.leaf 4456325723)) (.branch 6 (.leaf 4314591152) (.leaf 4178760753)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4048520182) (.leaf 3923575713)) (.branch 10 (.leaf 3803652587) (.leaf 3688493521))) (.branch 13 (.branch 12 (.leaf 3577857361) (.leaf 3471517865)) (.branch 14 (.leaf 3369262590) (.leaf 3270891885))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3176217971) (.branch 17 (.leaf 3085064098) (.leaf 2997263777))) (.branch 20 (.branch 19 (.leaf 2912660074) (.leaf 2831104959)) (.branch 21 (.leaf 2752458715) (.leaf 2676589385)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2603372267) (.leaf 2532689444)) (.branch 25 (.leaf 2464429357) (.leaf 2398486400))) (.branch 28 (.branch 27 (.leaf 2334760550) (.leaf 2273157022)) (.branch 29 (.leaf 2213585953) (.leaf 2155962102)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2100204572) (.branch 32 (.leaf 2046236556) (.leaf 1993985095))) (.branch 35 (.branch 34 (.leaf 1943380856) (.leaf 1894357920)) (.branch 36 (.leaf 1846853588) (.leaf 1800808199)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1756164961) (.leaf 1712869785)) (.branch 40 (.leaf 1670871143) (.leaf 1630119921))) (.branch 43 (.branch 42 (.leaf 1590569292) (.leaf 1552174588)) (.branch 44 (.leaf 1514893190) (.leaf 1478684411))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1443509400) (.branch 47 (.leaf 1409331044) (.leaf 1376113874))) (.branch 50 (.branch 49 (.leaf 1343823986) (.leaf 1312428954)) (.branch 51 (.leaf 1281897757) (.leaf 1252200710)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1223309392) (.leaf 1195196587)) (.branch 55 (.leaf 1167836221) (.leaf 1141203305))) (.branch 58 (.branch 57 (.leaf 1115273885) (.leaf 1090024989)) (.branch 59 (.leaf 1065434580) (.leaf 1041481509))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1018145476) (.branch 62 (.leaf 995406988) (.leaf 973247318))) (.branch 65 (.branch 64 (.leaf 951648473) (.leaf 930593160)) (.branch 66 (.leaf 910064748) (.leaf 890047243)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 870525258) (.leaf 851483983)) (.branch 70 (.leaf 832909161) (.leaf 814787060))) (.branch 73 (.branch 72 (.leaf 797104455) (.leaf 779848601)) (.branch 74 (.leaf 763007212) (.leaf 746568446))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 730520876) (.branch 77 (.leaf 714853484) (.leaf 699555633))) (.branch 80 (.branch 79 (.leaf 684617057) (.leaf 670027842)) (.branch 81 (.leaf 655778414) (.leaf 641859523)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 628262229) (.leaf 614977892)) (.branch 85 (.leaf 601998155) (.leaf 589314938))) (.branch 88 (.branch 87 (.leaf 576920422) (.leaf 564807043)) (.branch 89 (.leaf 552967478) (.leaf 541394637)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 530081655) (.branch 92 (.leaf 519021880) (.leaf 508208869))) (.branch 95 (.branch 94 (.leaf 497636377) (.leaf 487298350)) (.branch 96 (.leaf 477188919) (.leaf 467302391)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 457633244) (.leaf 448176121)) (.branch 100 (.leaf 438925822) (.leaf 429877299))) (.branch 103 (.branch 102 (.leaf 421025654) (.leaf 412366126)) (.branch 104 (.leaf 403894094) (.leaf 395605067))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 387494683) (.leaf 379558700)) (.branch 108 (.leaf 371792998) (.leaf 364193566))) (.branch 111 (.branch 110 (.leaf 356756510) (.leaf 349478036)) (.branch 112 (.leaf 342354459) (.leaf 335382191)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 328557739) (.leaf 321877705)) (.branch 116 (.leaf 315338782) (.leaf 308937749))) (.branch 119 (.branch 118 (.leaf 302671469) (.leaf 296536887)) (.branch 120 (.leaf 290531028) (.leaf 284650994)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 803).prefactor = (2306205330848063/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 803).cutoff/(generalMeanRows 803).c)).2 =
    (374817248206691/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 803).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 803).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 803).q*(generalMeanRows 803).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    have hcontinuation : (generalMeanRows 803).q*(generalMeanRows 803).cutoff/2-2 = (7814/3801:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable261.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 803).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 803

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 803).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 803).criticalRate j.val*(generalMeanRows 803).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 803).c*(generalMeanRows 803).criticalPoint j.val)).2-
      (generalMeanRows 803).J/2-(generalMeanRows 803).error (generalMeanGrid j.val)+
      (generalMeanRows 803).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 803).c)).2-
      (generalMeanRows 803).J/2-(generalMeanRows 803).error 4 := by
  have he : (generalMeanRows 803).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 803) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 803)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0803

/-! Kernel-checked entropy margins for general spectral rectangle 804. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0804
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4961652247) (.branch 2 (.leaf 4792374589) (.leaf 4630575772))) (.branch 5 (.branch 4 (.leaf 4475834896) (.leaf 4327760596)) (.branch 6 (.leaf 4185988466) (.leaf 4050178754)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3920014310) (.leaf 3795198739)) (.branch 10 (.leaf 3675454739) (.leaf 3560522605))) (.branch 13 (.branch 12 (.leaf 3450158872) (.leaf 3344135092)) (.branch 14 (.leaf 3242236713) (.leaf 3144262067))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3050021446) (.branch 17 (.leaf 2959336252) (.leaf 2872038226))) (.branch 20 (.branch 19 (.leaf 2787968736) (.leaf 2706978126)) (.branch 21 (.leaf 2628925117) (.leaf 2553676251)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2481105389) (.leaf 2411093230)) (.branch 25 (.leaf 2343526888) (.leaf 2278299478))) (.branch 28 (.branch 27 (.leaf 2215309749) (.leaf 2154461739)) (.branch 29 (.leaf 2095664448) (.leaf 2038831542)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1983881075) (.branch 32 (.leaf 1930735231) (.leaf 1879320076))) (.branch 35 (.branch 34 (.leaf 1829565343) (.leaf 1781404212)) (.branch 36 (.leaf 1734773118) (.leaf 1689611568)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1645861965) (.leaf 1603469451)) (.branch 40 (.leaf 1562381753) (.leaf 1522549044))) (.branch 43 (.branch 42 (.leaf 1483923809) (.leaf 1446460720)) (.branch 44 (.leaf 1410116520) (.leaf 1374849911))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1340621456) (.branch 47 (.leaf 1307393474) (.leaf 1275129955))) (.branch 50 (.branch 49 (.leaf 1243796470) (.leaf 1213360093)) (.branch 51 (.leaf 1183789322) (.leaf 1155054008)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1127125286) (.leaf 1099975514)) (.branch 55 (.leaf 1073578207) (.leaf 1047907987))) (.branch 58 (.branch 57 (.leaf 1022940522) (.leaf 998652479)) (.branch 59 (.leaf 975021476) (.leaf 952026034))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 929645536) (.branch 62 (.leaf 907860186) (.leaf 886650967))) (.branch 65 (.branch 64 (.leaf 865999610) (.leaf 845888556)) (.branch 66 (.leaf 826300923) (.leaf 807220476)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 788631599) (.leaf 770519261)) (.branch 70 (.leaf 752868997) (.leaf 735666879))) (.branch 73 (.branch 72 (.leaf 718899492) (.leaf 702553913)) (.branch 74 (.leaf 686617686) (.leaf 671078807))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 655925699) (.branch 77 (.leaf 641147198) (.leaf 626732532))) (.branch 80 (.branch 79 (.leaf 612671306) (.leaf 598953487)) (.branch 81 (.leaf 585569386) (.leaf 572509647)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 559765230) (.leaf 547327401)) (.branch 85 (.leaf 535187717) (.leaf 523338017))) (.branch 88 (.branch 87 (.leaf 511770408) (.leaf 500477254)) (.branch 89 (.leaf 489451170) (.leaf 478685006)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 468171844) (.branch 92 (.leaf 457904984) (.leaf 447877938))) (.branch 95 (.branch 94 (.leaf 438084422) (.leaf 428518347)) (.branch 96 (.leaf 419173812) (.leaf 410045099)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 401126662) (.leaf 392413124)) (.branch 100 (.leaf 383899271) (.leaf 375580042))) (.branch 103 (.branch 102 (.leaf 367450530) (.leaf 359505971)) (.branch 104 (.leaf 351741738) (.leaf 344153344))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 336736428) (.leaf 329486756)) (.branch 108 (.leaf 322400214) (.leaf 315472806))) (.branch 111 (.branch 110 (.leaf 308700649) (.leaf 302079967)) (.branch 112 (.leaf 295607091) (.leaf 289278454)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 283090587) (.leaf 277040116)) (.branch 116 (.leaf 271123759) (.leaf 265338322))) (.branch 119 (.branch 118 (.leaf 259680700) (.leaf 254147869)) (.branch 120 (.leaf 248736887) (.leaf 243444887)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 804).prefactor = (4645251429045243/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 804).cutoff/(generalMeanRows 804).c)).2 =
    (180109224392769/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 804).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 804).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 804).q*(generalMeanRows 804).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 804).q*(generalMeanRows 804).cutoff/2-2 = (7814/3801:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable261.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 804).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 804

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 804).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 804).criticalRate j.val*(generalMeanRows 804).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 804).c*(generalMeanRows 804).criticalPoint j.val)).2-
      (generalMeanRows 804).J/2-(generalMeanRows 804).error (generalMeanGrid j.val)+
      (generalMeanRows 804).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 804).c)).2-
      (generalMeanRows 804).J/2-(generalMeanRows 804).error 4 := by
  have he : (generalMeanRows 804).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 804) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 804)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0804

/-! Kernel-checked entropy margins for general spectral rectangle 805. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0805
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5001798185) (.branch 2 (.leaf 4831280539) (.leaf 4668269564))) (.branch 5 (.branch 4 (.leaf 4512344571) (.leaf 4363114325)) (.branch 6 (.leaf 4220214467) (.leaf 4083305229)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3952069373) (.leaf 3826210362)) (.branch 10 (.leaf 3705450696) (.leaf 3589530428))) (.branch 13 (.branch 12 (.leaf 3478205804) (.leaf 3371248051)) (.branch 14 (.leaf 3268442260) (.leaf 3169586373))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3074490267) (.branch 17 (.leaf 2982974908) (.leaf 2894871581))) (.branch 20 (.branch 19 (.leaf 2810021180) (.leaf 2728273564)) (.branch 21 (.leaf 2649486955) (.leaf 2573527392)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2500268218) (.leaf 2429589620)) (.branch 25 (.leaf 2361378186) (.leaf 2295526510))) (.branch 28 (.branch 27 (.leaf 2231932821) (.leaf 2170500633)) (.branch 29 (.leaf 2111138427) (.leaf 2053759355)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1998280960) (.branch 32 (.leaf 1944624917) (.leaf 1892716796))) (.branch 35 (.branch 34 (.leaf 1842485834) (.leaf 1793864726)) (.branch 36 (.leaf 1746789428) (.leaf 1701198975)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1657035311) (.leaf 1614243122)) (.branch 40 (.leaf 1572769693) (.leaf 1532564762))) (.branch 43 (.branch 42 (.leaf 1493580387) (.leaf 1455770825)) (.branch 44 (.leaf 1419092412) (.leaf 1383503456))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1348964130) (.branch 47 (.leaf 1315436377) (.leaf 1282883822))) (.branch 50 (.branch 49 (.leaf 1251271676) (.leaf 1220566666)) (.branch 51 (.leaf 1190736950) (.leaf 1161752052)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1133582788) (.leaf 1106201202)) (.branch 55 (.leaf 1079580512) (.leaf 1053695044))) (.branch 58 (.branch 57 (.leaf 1028520184) (.leaf 1004032324)) (.branch 59 (.leaf 980208815) (.leaf 957027920))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 934468771) (.branch 62 (.leaf 912511330) (.leaf 891136347))) (.branch 65 (.branch 64 (.leaf 870325325) (.leaf 850060485)) (.branch 66 (.leaf 830324733) (.leaf 811101630)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 792375359) (.leaf 774130699)) (.branch 70 (.leaf 756352999) (.leaf 739028153))) (.branch 73 (.branch 72 (.leaf 722142573) (.leaf 705683167)) (.branch 74 (.leaf 689637320) (.leaf 673992872))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 658738096) (.branch 77 (.leaf 643861682) (.leaf 629352720))) (.branch 80 (.branch 79 (.leaf 615200680) (.leaf 601395398)) (.branch 81 (.leaf 587927061) (.leaf 574786191)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 561963633) (.leaf 549450539)) (.branch 85 (.leaf 537238361) (.leaf 525318831))) (.branch 88 (.branch 87 (.leaf 513683955) (.leaf 502326004)) (.branch 89 (.leaf 491237497) (.leaf 480411196)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 469840095) (.branch 92 (.leaf 459517412) (.leaf 449436579))) (.branch 95 (.branch 94 (.leaf 439591235) (.leaf 429975216)) (.branch 96 (.leaf 420582551) (.leaf 411407452)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 402444307) (.leaf 393687677)) (.branch 100 (.leaf 385132286) (.leaf 376773014))) (.branch 103 (.branch 102 (.leaf 368604897) (.leaf 360623116)) (.branch 104 (.leaf 352822994) (.leaf 345199991))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 337749699) (.leaf 330467837)) (.branch 108 (.leaf 323350246) (.leaf 316392888))) (.branch 111 (.branch 110 (.leaf 309591836) (.leaf 302943276)) (.branch 112 (.leaf 296443502) (.leaf 290088908)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 283875989) (.leaf 277801339)) (.branch 116 (.leaf 271861642) (.leaf 266053674))) (.branch 119 (.branch 118 (.leaf 260374298) (.leaf 254820462)) (.branch 120 (.leaf 249389194) (.leaf 244077604)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 805).prefactor = (290799617124329/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 805).cutoff/(generalMeanRows 805).c)).2 =
    (44338599121821/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 805).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 805).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 805).q*(generalMeanRows 805).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 805).q*(generalMeanRows 805).cutoff/2-2 = (3886/1911:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable258.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 805).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 805

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 805).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 805).criticalRate j.val*(generalMeanRows 805).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 805).c*(generalMeanRows 805).criticalPoint j.val)).2-
      (generalMeanRows 805).J/2-(generalMeanRows 805).error (generalMeanGrid j.val)+
      (generalMeanRows 805).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 805).c)).2-
      (generalMeanRows 805).J/2-(generalMeanRows 805).error 4 := by
  have he : (generalMeanRows 805).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 805) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 805)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0805

/-! Kernel-checked entropy margins for general spectral rectangle 806. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0806
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5309823395) (.branch 2 (.leaf 5143425988) (.leaf 4984227406))) (.branch 5 (.branch 4 (.leaf 4831819365) (.leaf 4685822457)) (.branch 6 (.leaf 4545883628) (.leaf 4411673924)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4282886477) (.leaf 4159234694)) (.branch 10 (.leaf 4040450632) (.leaf 3926283525))) (.branch 13 (.branch 12 (.leaf 3816498462) (.leaf 3710875180)) (.branch 14 (.leaf 3609206969) (.leaf 3511299682))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3416970820) (.branch 17 (.leaf 3326048711) (.leaf 3238371742))) (.branch 20 (.branch 19 (.leaf 3153787670) (.leaf 3072152980)) (.branch 21 (.leaf 2993332295) (.leaf 2917197841)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2843628938) (.leaf 2772511550)) (.branch 25 (.leaf 2703737851) (.leaf 2637205833))) (.branch 28 (.branch 27 (.leaf 2572818942) (.leaf 2510485736)) (.branch 29 (.leaf 2450119572) (.leaf 2391638317)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2334964066) (.branch 32 (.leaf 2280022902) (.leaf 2226744647))) (.branch 35 (.branch 34 (.leaf 2175062651) (.leaf 2124913583)) (.branch 36 (.leaf 2076237240) (.leaf 2028976365)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1983076485) (.leaf 1938485747)) (.branch 40 (.leaf 1895154778) (.leaf 1853036541))) (.branch 43 (.branch 42 (.leaf 1812086212) (.leaf 1772261053)) (.branch 44 (.leaf 1733520303) (.leaf 1695825069))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1659138226) (.branch 47 (.leaf 1623424324) (.leaf 1588649498))) (.branch 50 (.branch 49 (.leaf 1554781385) (.leaf 1521789045)) (.branch 51 (.leaf 1489642890) (.leaf 1458314609)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1427777109) (.leaf 1398004449)) (.branch 55 (.leaf 1368971781) (.leaf 1340655298))) (.branch 58 (.branch 57 (.leaf 1313032180) (.leaf 1286080548)) (.branch 59 (.leaf 1259779413) (.leaf 1234108635))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1209048883) (.branch 62 (.leaf 1184581594) (.leaf 1160688936))) (.branch 65 (.branch 64 (.leaf 1137353773) (.leaf 1114559634)) (.branch 66 (.leaf 1092290680) (.leaf 1070531675)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1049267956) (.leaf 1028485411)) (.branch 70 (.leaf 1008170449) (.leaf 988309977))) (.branch 73 (.branch 72 (.leaf 968891382) (.leaf 949902503)) (.branch 74 (.leaf 931331616) (.leaf 913167410))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 895398973) (.branch 77 (.leaf 878015772) (.leaf 861007637))) (.branch 80 (.branch 79 (.leaf 844364748) (.leaf 828077613)) (.branch 81 (.leaf 812137062) (.leaf 796534230)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 781260542) (.leaf 766307704)) (.branch 85 (.leaf 751667693) (.leaf 737332738))) (.branch 88 (.branch 87 (.leaf 723295321) (.leaf 709548157)) (.branch 89 (.leaf 696084189) (.leaf 682896580)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 669978701) (.branch 92 (.leaf 657324126) (.leaf 644926622))) (.branch 95 (.branch 94 (.leaf 632780141) (.leaf 620878816)) (.branch 96 (.leaf 609216952) (.leaf 597789019)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 586589647) (.leaf 575613619)) (.branch 100 (.leaf 564855868) (.leaf 554311468))) (.branch 103 (.branch 102 (.leaf 543975630) (.leaf 533843698)) (.branch 104 (.leaf 523911145) (.leaf 514173566))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 504626676) (.leaf 495266303)) (.branch 108 (.leaf 486088389) (.leaf 477088979))) (.branch 111 (.branch 110 (.leaf 468264225) (.leaf 459610378)) (.branch 112 (.leaf 451123785) (.leaf 442800888)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 434638217) (.leaf 426632392)) (.branch 116 (.leaf 418780116) (.leaf 411078175))) (.branch 119 (.branch 118 (.leaf 403523434) (.leaf 396112836)) (.branch 120 (.leaf 388843397) (.leaf 381712205)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 806).prefactor = (283784994163571/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 806).cutoff/(generalMeanRows 806).c)).2 =
    (204110114879961/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 806).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 806).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 806).q*(generalMeanRows 806).c/2-2 = (1427/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable259.value]
    have hcontinuation : (generalMeanRows 806).q*(generalMeanRows 806).cutoff/2-2 = (7766/3731:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable262.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 806).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 806

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 806).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 806).criticalRate j.val*(generalMeanRows 806).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 806).c*(generalMeanRows 806).criticalPoint j.val)).2-
      (generalMeanRows 806).J/2-(generalMeanRows 806).error (generalMeanGrid j.val)+
      (generalMeanRows 806).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 806).c)).2-
      (generalMeanRows 806).J/2-(generalMeanRows 806).error 4 := by
  have he : (generalMeanRows 806).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 806) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 806)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0806

/-! Kernel-checked entropy margins for general spectral rectangle 807. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0807
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5214707074) (.branch 2 (.leaf 5046545165) (.leaf 4885657182))) (.branch 5 (.branch 4 (.leaf 4731634983) (.leaf 4584099100)) (.branch 6 (.leaf 4442696229) (.leaf 4307097001)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4176993973) (.leaf 4052099844)) (.branch 10 (.leaf 3932145836) (.leaf 3816880238))) (.branch 13 (.branch 12 (.leaf 3706067097) (.leaf 3599485017)) (.branch 14 (.leaf 3496926083) (.leaf 3398194875))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3303107563) (.branch 17 (.leaf 3211491095) (.leaf 3123182438))) (.branch 20 (.branch 19 (.leaf 3038027895) (.leaf 2955882467)) (.branch 21 (.leaf 2876609274) (.leaf 2800079021)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2726169500) (.leaf 2654765134)) (.branch 25 (.leaf 2585756559) (.leaf 2519040228))) (.branch 28 (.branch 27 (.leaf 2454518054) (.leaf 2392097069)) (.branch 29 (.leaf 2331689118) (.leaf 2273210562)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2216582015) (.branch 32 (.leaf 2161728088) (.leaf 2108577155))) (.branch 35 (.branch 34 (.leaf 2057061139) (.leaf 2007115301)) (.branch 36 (.leaf 1958678056) (.leaf 1911690790)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1866097694) (.leaf 1821845611)) (.branch 40 (.leaf 1778883886) (.leaf 1737164230))) (.branch 43 (.branch 42 (.leaf 1696640592) (.leaf 1657269037)) (.branch 44 (.leaf 1619007634) (.leaf 1581816348))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1545656941) (.branch 47 (.leaf 1510492878) (.leaf 1476289235))) (.branch 50 (.branch 49 (.leaf 1443012621) (.leaf 1410631095)) (.branch 51 (.leaf 1379114093) (.leaf 1348432360)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1318557882) (.leaf 1289463825)) (.branch 55 (.leaf 1261124475) (.leaf 1233515183))) (.branch 58 (.branch 57 (.leaf 1206612316) (.leaf 1180393202)) (.branch 59 (.leaf 1154836088) (.leaf 1129920093))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1105625169) (.branch 62 (.leaf 1081932056) (.leaf 1058822253))) (.branch 65 (.branch 64 (.leaf 1036277974) (.leaf 1014282122)) (.branch 66 (.leaf 992818250) (.leaf 971870538)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 951423758) (.leaf 931463252)) (.branch 70 (.leaf 911974905) (.leaf 892945117))) (.branch 73 (.branch 72 (.leaf 874360785) (.leaf 856209280)) (.branch 74 (.leaf 838478422) (.leaf 821156468))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 804232084) (.branch 77 (.leaf 787694334) (.leaf 771532661))) (.branch 80 (.branch 79 (.leaf 755736871) (.leaf 740297116)) (.branch 81 (.leaf 725203881) (.leaf 710447973)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 696020499) (.leaf 681912865)) (.branch 85 (.leaf 668116753) (.leaf 654624120))) (.branch 88 (.branch 87 (.leaf 641427177) (.leaf 628518387)) (.branch 89 (.leaf 615890451) (.leaf 603536296)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 591449075) (.branch 92 (.leaf 579622147) (.leaf 568049080))) (.branch 95 (.branch 94 (.leaf 556723632) (.leaf 545639755)) (.branch 96 (.leaf 534791578) (.leaf 524173407)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 513779714) (.leaf 503605135)) (.branch 100 (.leaf 493644459) (.leaf 483892627))) (.branch 103 (.branch 102 (.leaf 474344725) (.leaf 464995978)) (.branch 104 (.leaf 455841745) (.leaf 446877517))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 438098906) (.leaf 429501650)) (.branch 108 (.leaf 421081602) (.leaf 412834725))) (.branch 111 (.branch 110 (.leaf 404757095) (.leaf 396844891)) (.branch 112 (.leaf 389094395) (.leaf 381501987)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 374064141) (.leaf 366777425)) (.branch 116 (.leaf 359638495) (.leaf 352644093))) (.branch 119 (.branch 118 (.leaf 345791046) (.leaf 339076260)) (.branch 120 (.leaf 332496720) (.leaf 326049487)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 807).prefactor = (569314997349073/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 807).cutoff/(generalMeanRows 807).c)).2 =
    (382476073442591/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 807).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 807).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 807).q*(generalMeanRows 807).c/2-2 = (377/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable247.value]
    have hcontinuation : (generalMeanRows 807).q*(generalMeanRows 807).cutoff/2-2 = (1921/943:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable260.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 807).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 807

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 807).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 807).criticalRate j.val*(generalMeanRows 807).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 807).c*(generalMeanRows 807).criticalPoint j.val)).2-
      (generalMeanRows 807).J/2-(generalMeanRows 807).error (generalMeanGrid j.val)+
      (generalMeanRows 807).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 807).c)).2-
      (generalMeanRows 807).J/2-(generalMeanRows 807).error 4 := by
  have he : (generalMeanRows 807).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 807) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 807)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0807

/-! Kernel-checked entropy margins for general spectral rectangle 808. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0808
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5261356609) (.branch 2 (.leaf 5094055150) (.leaf 4933990559))) (.branch 5 (.branch 4 (.leaf 4780754632) (.leaf 4633967937)) (.branch 6 (.leaf 4493277303) (.leaf 4358353570)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4228889585) (.leaf 4104598402)) (.branch 10 (.leaf 3985211659) (.leaf 3870478117))) (.branch 13 (.branch 12 (.leaf 3760162340) (.leaf 3654043496)) (.branch 14 (.leaf 3551914268) (.leaf 3453579867))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3358857126) (.branch 17 (.leaf 3267573674) (.leaf 3179567184))) (.branch 20 (.branch 19 (.leaf 3094684679) (.leaf 3012781895)) (.branch 21 (.leaf 2933722697) (.leaf 2857378543)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2783627983) (.leaf 2712356202)) (.branch 25 (.leaf 2643454598) (.leaf 2576820387))) (.branch 28 (.branch 27 (.leaf 2512356240) (.leaf 2449969945)) (.branch 29 (.leaf 2389574095) (.leaf 2331085797)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2274426400) (.branch 32 (.leaf 2219521240) (.leaf 2166299412))) (.branch 35 (.branch 34 (.leaf 2114693542) (.leaf 2064639591)) (.branch 36 (.leaf 2016076655) (.leaf 1968946793)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1923194858) (.leaf 1878768338)) (.branch 40 (.leaf 1835617212) (.leaf 1793693811))) (.branch 43 (.branch 42 (.leaf 1752952690) (.leaf 1713350508)) (.branch 44 (.leaf 1674845912) (.leaf 1637399432))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1600973381) (.branch 47 (.leaf 1565531759) (.leaf 1531040168))) (.branch 50 (.branch 49 (.leaf 1497465725) (.leaf 1464776983)) (.branch 51 (.leaf 1432943860) (.leaf 1401937570)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1371730553) (.leaf 1342296415)) (.branch 55 (.leaf 1313609871) (.leaf 1285646689))) (.branch 58 (.branch 57 (.leaf 1258383636) (.leaf 1231798433)) (.branch 59 (.leaf 1205869703) (.leaf 1180576932))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1155900424) (.branch 62 (.leaf 1131821265) (.leaf 1108321282))) (.branch 65 (.branch 64 (.leaf 1085383012) (.leaf 1062989665)) (.branch 66 (.leaf 1041125095) (.leaf 1019773767)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 998920735) (.leaf 978551607)) (.branch 70 (.leaf 958652527) (.leaf 939210145))) (.branch 73 (.branch 72 (.leaf 920211599) (.leaf 901644489)) (.branch 74 (.leaf 883496860) (.leaf 865757181))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 848414326) (.branch 77 (.leaf 831457556) (.leaf 814876505))) (.branch 80 (.branch 79 (.leaf 798661160) (.leaf 782801849)) (.branch 81 (.leaf 767289227) (.leaf 752114260)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 737268211) (.leaf 722742633)) (.branch 85 (.leaf 708529352) (.leaf 694620458))) (.branch 88 (.branch 87 (.leaf 681008294) (.leaf 667685446)) (.branch 89 (.leaf 654644731) (.leaf 641879194)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 629382092) (.branch 92 (.leaf 617146890) (.leaf 605167250))) (.branch 95 (.branch 94 (.leaf 593437027) (.leaf 581950258)) (.branch 96 (.leaf 570701159) (.leaf 559684114)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 548893672) (.leaf 538324539)) (.branch 100 (.leaf 527971574) (.leaf 517829782))) (.branch 103 (.branch 102 (.leaf 507894308) (.leaf 498160434)) (.branch 104 (.leaf 488623574) (.leaf 479279268))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 470123178) (.leaf 461151084)) (.branch 108 (.leaf 452358879) (.leaf 443742568))) (.branch 111 (.branch 110 (.leaf 435298261) (.leaf 427022171)) (.branch 112 (.leaf 418910610) (.leaf 410959986)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 403166801) (.leaf 395527645)) (.branch 116 (.leaf 388039196) (.leaf 380698215))) (.branch 119 (.branch 118 (.leaf 373501548) (.leaf 366446115)) (.branch 120 (.leaf 359528916) (.leaf 352747023)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 808).prefactor = (4547483864124269/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 808).cutoff/(generalMeanRows 808).c)).2 =
    (19765289275389/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 808).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 808).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 808).q*(generalMeanRows 808).c/2-2 = (587/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable263.value]
    have hcontinuation : (generalMeanRows 808).q*(generalMeanRows 808).cutoff/2-2 = (5150/2501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable264.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 808).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 808

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 808).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 808).criticalRate j.val*(generalMeanRows 808).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 808).c*(generalMeanRows 808).criticalPoint j.val)).2-
      (generalMeanRows 808).J/2-(generalMeanRows 808).error (generalMeanGrid j.val)+
      (generalMeanRows 808).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 808).c)).2-
      (generalMeanRows 808).J/2-(generalMeanRows 808).error 4 := by
  have he : (generalMeanRows 808).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 808) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 808)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0808

/-! Kernel-checked entropy margins for general spectral rectangle 809. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0809
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5212378796) (.branch 2 (.leaf 5044224040) (.leaf 4883368348))) (.branch 5 (.branch 4 (.leaf 4729400432) (.leaf 4581937966)) (.branch 6 (.leaf 4440625055) (.leaf 4305129974)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4175143154) (.leaf 4050375362)) (.branch 10 (.leaf 3930556078) (.leaf 3815432018))) (.branch 13 (.branch 12 (.leaf 3704765810) (.leaf 3598334782)) (.branch 14 (.leaf 3495929874) (.leaf 3397354635))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3302424322) (.branch 17 (.leaf 3210965060) (.leaf 3122813091))) (.branch 20 (.branch 19 (.leaf 3037814071) (.leaf 2955822435)) (.branch 21 (.leaf 2876700802) (.leaf 2800319442)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2726555768) (.leaf 2655293878)) (.branch 25 (.leaf 2586424129) (.leaf 2519842740))) (.branch 28 (.branch 27 (.leaf 2455451428) (.leaf 2393157066)) (.branch 29 (.leaf 2332871370) (.leaf 2274510606)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2217995312) (.branch 32 (.leaf 2163250054) (.leaf 2110203179))) (.branch 35 (.branch 34 (.leaf 2058786600) (.leaf 2008935589)) (.branch 36 (.leaf 1960588584) (.leaf 1913687011)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1868175109) (.leaf 1823999782)) (.branch 40 (.leaf 1781110444) (.leaf 1739458884))) (.branch 43 (.branch 42 (.leaf 1698999135) (.leaf 1659687352)) (.branch 44 (.leaf 1621481699) (.leaf 1584342241))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1548230842) (.branch 47 (.leaf 1513111072) (.leaf 1478948116))) (.branch 50 (.branch 49 (.leaf 1445708690) (.leaf 1413360965)) (.branch 51 (.leaf 1381874488) (.leaf 1351220113)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1321369937) (.leaf 1292297237)) (.branch 55 (.leaf 1263976407) (.leaf 1236382909))) (.branch 58 (.branch 57 (.leaf 1209493215) (.leaf 1183284759)) (.branch 59 (.leaf 1157735891) (.leaf 1132825834))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1108534638) (.branch 62 (.leaf 1084843144) (.leaf 1061732943))) (.branch 65 (.branch 64 (.leaf 1039186346) (.leaf 1017186346)) (.branch 66 (.leaf 995716585) (.leaf 974761330)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 954305437) (.leaf 934334331)) (.branch 70 (.leaf 914833974) (.leaf 895790846))) (.branch 73 (.branch 72 (.leaf 877191917) (.leaf 859024630)) (.branch 74 (.leaf 841276876) (.leaf 823936978))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 806993668) (.branch 77 (.leaf 790436073) (.leaf 774253695))) (.branch 80 (.branch 79 (.leaf 758436400) (.leaf 742974395)) (.branch 81 (.leaf 727858221) (.leaf 713078733)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 698627092) (.leaf 684494748)) (.branch 85 (.leaf 670673432) (.leaf 657155143))) (.branch 88 (.branch 87 (.leaf 643932135) (.leaf 630996911)) (.branch 89 (.leaf 618342208) (.leaf 605960995)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 593846456) (.branch 92 (.leaf 581991985) (.leaf 570391181))) (.branch 95 (.branch 94 (.leaf 559037835) (.leaf 547925925)) (.branch 96 (.leaf 537049609) (.leaf 526403218)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 515981251) (.leaf 505778365)) (.branch 100 (.leaf 495789374) (.leaf 486009240))) (.branch 103 (.branch 102 (.leaf 476433067) (.leaf 467056101)) (.branch 104 (.leaf 457873718) (.leaf 448881425))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 440074853) (.leaf 431449752)) (.branch 108 (.leaf 423001990) (.leaf 414727544))) (.branch 111 (.branch 110 (.leaf 406622501) (.leaf 398683053)) (.branch 112 (.leaf 390905493) (.leaf 383286209)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 375821687) (.leaf 368508502)) (.branch 116 (.leaf 361343319) (.leaf 354322888))) (.branch 119 (.branch 118 (.leaf 347444041) (.leaf 340703692)) (.branch 120 (.leaf 334098831) (.leaf 327626525)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 809).prefactor = (2289877544769717/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 809).cutoff/(generalMeanRows 809).c)).2 =
    (193962839105079/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 809).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 809).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 809).q*(generalMeanRows 809).c/2-2 = (377/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable247.value]
    have hcontinuation : (generalMeanRows 809).q*(generalMeanRows 809).cutoff/2-2 = (5150/2501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable264.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 809).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 809

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 809).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 809).criticalRate j.val*(generalMeanRows 809).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 809).c*(generalMeanRows 809).criticalPoint j.val)).2-
      (generalMeanRows 809).J/2-(generalMeanRows 809).error (generalMeanGrid j.val)+
      (generalMeanRows 809).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 809).c)).2-
      (generalMeanRows 809).J/2-(generalMeanRows 809).error 4 := by
  have he : (generalMeanRows 809).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 809) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 809)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0809

/-! Kernel-checked entropy margins for general spectral rectangle 810. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0810
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5167582634) (.branch 2 (.leaf 4998578459) (.leaf 4836911147))) (.branch 5 (.branch 4 (.leaf 4682169389) (.leaf 4533970745)) (.branch 6 (.leaf 4391959114) (.leaf 4255802495)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4125190963) (.leaf 3999834874)) (.branch 10 (.leaf 3879463231) (.leaf 3763822231))) (.branch 13 (.branch 12 (.leaf 3652673931) (.leaf 3545795053)) (.branch 14 (.leaf 3442975893) (.leaf 3344019330))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3248739921) (.branch 17 (.leaf 3156963074) (.leaf 3068524292))) (.branch 20 (.branch 19 (.leaf 2983268481) (.leaf 2901049311)) (.branch 21 (.leaf 2821728631) (.leaf 2745175931)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2671267843) (.leaf 2599887684)) (.branch 25 (.leaf 2530925027) (.leaf 2464275311))) (.branch 28 (.branch 27 (.leaf 2399839477) (.leaf 2337523628)) (.branch 29 (.leaf 2277238714) (.leaf 2218900244)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2162428011) (.branch 32 (.leaf 2107745840) (.leaf 2054781352))) (.branch 35 (.branch 34 (.leaf 2003465745) (.leaf 1953733586)) (.branch 36 (.leaf 1905522622) (.leaf 1858773599)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1813430093) (.leaf 1769438354)) (.branch 40 (.leaf 1726747159) (.leaf 1685307674))) (.branch 43 (.branch 42 (.leaf 1645073321) (.leaf 1605999663)) (.branch 44 (.leaf 1568044282) (.leaf 1531166677))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1495328161) (.branch 47 (.leaf 1460491767) (.leaf 1426622157))) (.branch 50 (.branch 49 (.leaf 1393685541) (.leaf 1361649592)) (.branch 51 (.leaf 1330483380) (.leaf 1300157293)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1270642975) (.leaf 1241913264)) (.branch 55 (.leaf 1213942129) (.leaf 1186704620))) (.branch 58 (.branch 57 (.leaf 1160176809) (.leaf 1134335745)) (.branch 59 (.leaf 1109159403) (.leaf 1084626644))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1060717168) (.branch 62 (.leaf 1037411478) (.leaf 1014690839))) (.branch 65 (.branch 64 (.leaf 992537247) (.leaf 970933389)) (.branch 66 (.leaf 949862615) (.leaf 929308908)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 909256852) (.leaf 889691608)) (.branch 70 (.leaf 870598886) (.leaf 851964920))) (.branch 73 (.branch 72 (.leaf 833776448) (.leaf 816020686)) (.branch 74 (.leaf 798685309) (.leaf 781758430))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 765228583) (.branch 77 (.leaf 749084702) (.leaf 733316105))) (.branch 80 (.branch 79 (.leaf 717912480) (.leaf 702863867)) (.branch 81 (.leaf 688160642) (.leaf 673793507)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 659753472) (.leaf 646031848)) (.branch 85 (.leaf 632620228) (.leaf 619510482))) (.branch 88 (.branch 87 (.leaf 606694739) (.leaf 594165385)) (.branch 89 (.leaf 581915046) (.leaf 569936580)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 558223072) (.branch 92 (.leaf 546767819) (.leaf 535564326))) (.branch 95 (.branch 94 (.leaf 524606297) (.leaf 513887628)) (.branch 96 (.leaf 503402399) (.leaf 493144866)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 483109457) (.leaf 473290764)) (.branch 100 (.leaf 463683537) (.leaf 454282681))) (.branch 103 (.branch 102 (.leaf 445083244) (.leaf 436080420)) (.branch 104 (.leaf 427269536) (.leaf 418646055))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 410205565) (.leaf 401943778)) (.branch 108 (.leaf 393856522) (.leaf 385939744))) (.branch 111 (.branch 110 (.leaf 378189499) (.leaf 370601950)) (.branch 112 (.leaf 363173363) (.leaf 355900104)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 348778636) (.leaf 341805516)) (.branch 116 (.leaf 334977391) (.leaf 328290996))) (.branch 119 (.branch 118 (.leaf 321743150) (.leaf 315330754)) (.branch 120 (.leaf 309050791) (.leaf 302900318)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 810).prefactor = (45874058448899/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 810).cutoff/(generalMeanRows 810).c)).2 =
    (375150033350519/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 810).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 810).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 810).q*(generalMeanRows 810).c/2-2 = (3097/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable249.value]
    have hcontinuation : (generalMeanRows 810).q*(generalMeanRows 810).cutoff/2-2 = (1921/943:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable260.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 810).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 810

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 810).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 810).criticalRate j.val*(generalMeanRows 810).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 810).c*(generalMeanRows 810).criticalPoint j.val)).2-
      (generalMeanRows 810).J/2-(generalMeanRows 810).error (generalMeanGrid j.val)+
      (generalMeanRows 810).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 810).c)).2-
      (generalMeanRows 810).J/2-(generalMeanRows 810).error 4 := by
  have he : (generalMeanRows 810).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 810) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 810)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0810

/-! Kernel-checked entropy margins for general spectral rectangle 811. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0811
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5121291165) (.branch 2 (.leaf 4951473981) (.leaf 4789056672))) (.branch 5 (.branch 4 (.leaf 4633624713) (.leaf 4484792645)) (.branch 6 (.leaf 4342201531) (.leaf 4205516693)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4074425690) (.leaf 3948636496)) (.branch 10 (.leaf 3827875870) (.leaf 3711887878))) (.branch 13 (.branch 12 (.leaf 3600432564) (.leaf 3493284739)) (.branch 14 (.leaf 3390232886) (.leaf 3291078163))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3195633487) (.branch 17 (.leaf 3103722711) (.leaf 3015179854))) (.branch 20 (.branch 19 (.leaf 2929848409) (.leaf 2847580699)) (.branch 21 (.leaf 2768237287) (.leaf 2691686439)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2617803613) (.leaf 2546471007)) (.branch 25 (.leaf 2477577125) (.leaf 2411016381))) (.branch 28 (.branch 27 (.leaf 2346688738) (.leaf 2284499359)) (.branch 29 (.leaf 2224358300) (.leaf 2166180209)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2109884053) (.branch 32 (.leaf 2055392870) (.leaf 2002633523))) (.branch 35 (.branch 34 (.leaf 1951536483) (.leaf 1902035622)) (.branch 36 (.leaf 1854068017) (.leaf 1807573774)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1762495853) (.leaf 1718779914)) (.branch 40 (.leaf 1676374166) (.leaf 1635229230))) (.branch 43 (.branch 42 (.leaf 1595298006) (.leaf 1556535553)) (.branch 44 (.leaf 1518898971) (.leaf 1482347296))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1446841396) (.branch 47 (.leaf 1412343875) (.leaf 1378818984))) (.branch 50 (.branch 49 (.leaf 1346232538) (.leaf 1314551833)) (.branch 51 (.leaf 1283745571) (.leaf 1253783791)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1224637802) (.leaf 1196280117)) (.branch 55 (.leaf 1168684397) (.leaf 1141825391))) (.branch 58 (.branch 57 (.leaf 1115678886) (.leaf 1090221656)) (.branch 59 (.leaf 1065431412) (.leaf 1041286761))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1017767161) (.branch 62 (.leaf 994852880) (.leaf 972524961))) (.branch 65 (.branch 64 (.leaf 950765182) (.leaf 929556026)) (.branch 66 (.leaf 908880645) (.leaf 888722832)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 869066989) (.leaf 849898104)) (.branch 70 (.leaf 831201718) (.leaf 812963908))) (.branch 73 (.branch 72 (.leaf 795171257) (.leaf 777810836)) (.branch 74 (.leaf 760870179) (.leaf 744337266))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 728200502) (.branch 77 (.leaf 712448699) (.leaf 697071059))) (.branch 80 (.branch 79 (.leaf 682057158) (.leaf 667396929)) (.branch 81 (.leaf 653080648) (.leaf 639098919)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 625442662) (.leaf 612103098)) (.branch 85 (.leaf 599071738) (.leaf 586340373))) (.branch 88 (.branch 87 (.leaf 573901057) (.leaf 561746105)) (.branch 89 (.leaf 549868074) (.leaf 538259761)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 526914187) (.branch 92 (.leaf 515824594) (.leaf 504984434))) (.branch 95 (.branch 94 (.leaf 494387359) (.leaf 484027217)) (.branch 96 (.leaf 473898043) (.leaf 463994053)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 454309634) (.leaf 444839342)) (.branch 100 (.leaf 435577893) (.leaf 426520158))) (.branch 103 (.branch 102 (.leaf 417661159) (.leaf 408996061)) (.branch 104 (.leaf 400520167) (.leaf 392228915))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 384117874) (.leaf 376182736)) (.branch 108 (.leaf 368419314) (.leaf 360823537))) (.branch 111 (.branch 110 (.leaf 353391448) (.leaf 346119197)) (.branch 112 (.leaf 339003040) (.leaf 332039336)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 325224539) (.leaf 318555200)) (.branch 116 (.leaf 312027962) (.leaf 305639556))) (.branch 119 (.branch 118 (.leaf 299386800) (.leaf 293266596)) (.branch 120 (.leaf 287275924) (.leaf 281411845)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 811).prefactor = (4620529163055491/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 811).cutoff/(generalMeanRows 811).c)).2 =
    (1149616481317/3125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 811).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 811).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 811).q*(generalMeanRows 811).c/2-2 = (1589/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable251.value]
    have hcontinuation : (generalMeanRows 811).q*(generalMeanRows 811).cutoff/2-2 = (1921/943:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable260.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 811).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 811

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 811).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 811).criticalRate j.val*(generalMeanRows 811).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 811).c*(generalMeanRows 811).criticalPoint j.val)).2-
      (generalMeanRows 811).J/2-(generalMeanRows 811).error (generalMeanGrid j.val)+
      (generalMeanRows 811).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 811).c)).2-
      (generalMeanRows 811).J/2-(generalMeanRows 811).error 4 := by
  have he : (generalMeanRows 811).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 811) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 811)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0811

/-! Kernel-checked entropy margins for general spectral rectangle 812. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0812
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4916991681) (.branch 2 (.leaf 4747007423) (.leaf 4584563712))) (.branch 5 (.branch 4 (.leaf 4429236367) (.leaf 4280630941)) (.branch 6 (.leaf 4138380133) (.leaf 4002141468)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3871595229) (.leaf 3746442597)) (.branch 10 (.leaf 3626403986) (.leaf 3511217525))) (.branch 13 (.branch 12 (.leaf 3400637706) (.leaf 3294434139)) (.branch 14 (.leaf 3192390435) (.leaf 3094303182))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2999981016) (.branch 17 (.leaf 2909243764) (.leaf 2821921670))) (.branch 20 (.branch 19 (.leaf 2737854679) (.leaf 2656891777)) (.branch 21 (.leaf 2578890394) (.leaf 2503715842)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2431240804) (.leaf 2361344863)) (.branch 25 (.leaf 2293914061) (.leaf 2228840493))) (.branch 28 (.branch 27 (.leaf 2166021933) (.leaf 2105361487)) (.branch 29 (.leaf 2046767264) (.leaf 1990152080)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1935433175) (.branch 32 (.leaf 1882531952) (.leaf 1831373734))) (.branch 35 (.branch 34 (.leaf 1781887541) (.leaf 1734005869)) (.branch 36 (.leaf 1687664502) (.leaf 1642802320)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1599361128) (.leaf 1557285495)) (.branch 40 (.leaf 1516522598) (.leaf 1477022085))) (.branch 43 (.branch 42 (.leaf 1438735937) (.leaf 1401618344)) (.branch 44 (.leaf 1365625586) (.leaf 1330715924))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1296849496) (.branch 47 (.leaf 1263988215) (.leaf 1232095682))) (.branch 50 (.branch 49 (.leaf 1201137097) (.leaf 1171079177)) (.branch 51 (.leaf 1141890078) (.leaf 1113539323)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1085997738) (.leaf 1059237377)) (.branch 55 (.leaf 1033231472) (.leaf 1007954369))) (.branch 58 (.branch 57 (.leaf 983381474) (.leaf 959489205)) (.branch 59 (.leaf 936254937) (.leaf 913656965))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 891674450) (.branch 62 (.leaf 870287388) (.leaf 849476563))) (.branch 65 (.branch 64 (.leaf 829223515) (.leaf 809510501)) (.branch 66 (.leaf 790320468) (.leaf 771637014)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 753444364) (.leaf 735727338)) (.branch 70 (.leaf 718471329) (.leaf 701662270))) (.branch 73 (.branch 72 (.leaf 685286618) (.leaf 669331325)) (.branch 74 (.leaf 653783821) (.leaf 638631988))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 623864145) (.branch 77 (.leaf 609469027) (.leaf 595435769))) (.branch 80 (.branch 79 (.leaf 581753886) (.leaf 568413259)) (.branch 81 (.leaf 555404120) (.leaf 542717038)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 530342902) (.leaf 518272912)) (.branch 85 (.leaf 506498560) (.leaf 495011628))) (.branch 88 (.branch 87 (.leaf 483804167) (.leaf 472868491)) (.branch 89 (.leaf 462197165) (.leaf 451782996)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 441619024) (.branch 92 (.leaf 431698510) (.leaf 422014931))) (.branch 95 (.branch 94 (.leaf 412561971) (.leaf 403333510)) (.branch 96 (.leaf 394323622) (.leaf 385526561)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 376936761) (.leaf 368548826)) (.branch 100 (.leaf 360357522) (.leaf 352357775))) (.branch 103 (.branch 102 (.leaf 344544662) (.leaf 336913407)) (.branch 104 (.leaf 329459378) (.leaf 322178075))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 315065134) (.leaf 308116316)) (.branch 108 (.leaf 301327504) (.leaf 294694700))) (.branch 111 (.branch 110 (.leaf 288214022) (.leaf 281881696)) (.branch 112 (.leaf 275694055) (.leaf 269647537)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 263738679) (.leaf 257964112)) (.branch 116 (.leaf 252320562) (.leaf 246804845))) (.branch 119 (.branch 118 (.leaf 241413865) (.leaf 236144609)) (.branch 120 (.leaf 230994146) (.leaf 225959623)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 812).prefactor = (2339163012765201/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 812).cutoff/(generalMeanRows 812).c)).2 =
    (88249550203013/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 812).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 812).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 812).q*(generalMeanRows 812).c/2-2 = (1699/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable222.value]
    have hcontinuation : (generalMeanRows 812).q*(generalMeanRows 812).cutoff/2-2 = (7814/3801:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable261.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 812).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 812

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 812).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 812).criticalRate j.val*(generalMeanRows 812).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 812).c*(generalMeanRows 812).criticalPoint j.val)).2-
      (generalMeanRows 812).J/2-(generalMeanRows 812).error (generalMeanGrid j.val)+
      (generalMeanRows 812).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 812).c)).2-
      (generalMeanRows 812).J/2-(generalMeanRows 812).error 4 := by
  have he : (generalMeanRows 812).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 812) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 812)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0812

/-! Kernel-checked entropy margins for general spectral rectangle 813. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0813
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5058230901) (.branch 2 (.leaf 4887915580) (.leaf 4725108676))) (.branch 5 (.branch 4 (.leaf 4569386482) (.leaf 4420355084)) (.branch 6 (.leaf 4277647766) (.leaf 4140922685)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4009860796) (.leaf 3884163990)) (.branch 10 (.leaf 3763553414) (.leaf 3647767965))) (.branch 13 (.branch 12 (.leaf 3536562917) (.leaf 3429708684)) (.branch 14 (.leaf 3326989693) (.leaf 3228203360))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3133159155) (.branch 17 (.leaf 3041677746) (.leaf 2953590221))) (.branch 20 (.branch 19 (.leaf 2868737366) (.leaf 2786969013)) (.branch 21 (.leaf 2708143426) (.leaf 2632126753)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2558792503) (.leaf 2488021077)) (.branch 25 (.leaf 2419699326) (.leaf 2353720144))) (.branch 28 (.branch 27 (.leaf 2289982094) (.leaf 2228389054)) (.branch 29 (.leaf 2168849898) (.leaf 2111278189)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2055591901) (.branch 32 (.leaf 2001713158) (.leaf 1949567987))) (.branch 35 (.branch 34 (.leaf 1899086096) (.leaf 1850200656)) (.branch 36 (.leaf 1802848107) (.leaf 1756967969)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1712502673) (.leaf 1669397396)) (.branch 40 (.leaf 1627599908) (.leaf 1587060430))) (.branch 43 (.branch 42 (.leaf 1547731504) (.leaf 1509567861)) (.branch 44 (.leaf 1472526310) (.leaf 1436565620))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1401646423) (.branch 47 (.leaf 1367731113) (.leaf 1334783754))) (.branch 50 (.branch 49 (.leaf 1302769991) (.leaf 1271656974)) (.branch 51 (.leaf 1241413277) (.leaf 1212008827)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1183414834) (.leaf 1155603730)) (.branch 55 (.leaf 1128549104) (.leaf 1102225649))) (.branch 58 (.branch 57 (.leaf 1076609105) (.leaf 1051676206)) (.branch 59 (.leaf 1027404636) (.leaf 1003772983))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 980760692) (.branch 62 (.leaf 958348025) (.leaf 936516025))) (.branch 65 (.branch 64 (.leaf 915246479) (.leaf 894521880)) (.branch 66 (.leaf 874325397) (.leaf 854640842)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 835452645) (.leaf 816745818)) (.branch 70 (.leaf 798505937) (.leaf 780719111))) (.branch 73 (.branch 72 (.leaf 763371959) (.leaf 746451591)) (.branch 74 (.leaf 729945583) (.leaf 713841955))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 698129157) (.branch 77 (.leaf 682796047) (.leaf 667831873))) (.branch 80 (.branch 79 (.leaf 653226258) (.leaf 638969184)) (.branch 81 (.leaf 625050975) (.leaf 611462286)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 598194085) (.leaf 585237645)) (.branch 85 (.leaf 572584529) (.leaf 560226575))) (.branch 88 (.branch 87 (.leaf 548155893) (.leaf 536364844)) (.branch 89 (.leaf 524846040) (.leaf 513592328)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 502596779) (.branch 92 (.leaf 491852687) (.leaf 481353554))) (.branch 95 (.branch 94 (.leaf 471093082) (.leaf 461065171)) (.branch 96 (.leaf 451263904) (.leaf 441683545)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 432318534) (.leaf 423163472)) (.branch 100 (.leaf 414213126) (.leaf 405462415))) (.branch 103 (.branch 102 (.leaf 396906406) (.leaf 388540313)) (.branch 104 (.leaf 380359486) (.leaf 372359409))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 364535696) (.leaf 356884084)) (.branch 108 (.leaf 349400433) (.leaf 342080715))) (.branch 111 (.branch 110 (.leaf 334921017) (.leaf 327917534)) (.branch 112 (.leaf 321066564) (.leaf 314364508)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 307807863) (.leaf 301393222)) (.branch 116 (.leaf 295117269) (.leaf 288976777))) (.branch 119 (.branch 118 (.leaf 282968602) (.leaf 277089688)) (.branch 120 (.leaf 271337053) (.leaf 265707799)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 813).prefactor = (4674292047606109/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 813).cutoff/(generalMeanRows 813).c)).2 =
    (37025746160751/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 813).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 813).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 813).q*(generalMeanRows 813).c/2-2 = (1617/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable243.value]
    have hcontinuation : (generalMeanRows 813).q*(generalMeanRows 813).cutoff/2-2 = (15670/7581:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable265.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 813).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 813

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 813).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 813).criticalRate j.val*(generalMeanRows 813).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 813).c*(generalMeanRows 813).criticalPoint j.val)).2-
      (generalMeanRows 813).J/2-(generalMeanRows 813).error (generalMeanGrid j.val)+
      (generalMeanRows 813).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 813).c)).2-
      (generalMeanRows 813).J/2-(generalMeanRows 813).error 4 := by
  have he : (generalMeanRows 813).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 813) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 813)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0813

/-! Kernel-checked entropy margins for general spectral rectangle 814. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0814
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4994196881) (.branch 2 (.leaf 4823750203) (.leaf 4660847412))) (.branch 5 (.branch 4 (.leaf 4505063047) (.leaf 4356001534)) (.branch 6 (.leaf 4213294585) (.leaf 4076598864)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3945593910) (.leaf 3819980265)) (.branch 10 (.leaf 3699477795) (.leaf 3583824174))) (.branch 13 (.branch 12 (.leaf 3472773508) (.leaf 3366095100)) (.branch 14 (.leaf 3263572312) (.leaf 3165001544))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3070191293) (.branch 17 (.leaf 2978961296) (.leaf 2891141748))) (.branch 20 (.branch 19 (.leaf 2806572581) (.leaf 2725102806)) (.branch 21 (.leaf 2646589904) (.leaf 2570899264)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2497903675) (.leaf 2427482840)) (.branch 25 (.leaf 2359522942) (.leaf 2293916236))) (.branch 28 (.branch 27 (.leaf 2230560665) (.leaf 2169359518)) (.branch 29 (.leaf 2110221096) (.leaf 2053058417)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1997788927) (.branch 32 (.leaf 1944334243) (.leaf 1892619907))) (.branch 35 (.branch 34 (.leaf 1842575157) (.leaf 1794132714)) (.branch 36 (.leaf 1747228585) (.leaf 1701801873)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1657794610) (.leaf 1615151585)) (.branch 40 (.leaf 1573820200) (.leaf 1533750319))) (.branch 43 (.branch 42 (.leaf 1494894140) (.leaf 1457206067)) (.branch 44 (.leaf 1420642591) (.leaf 1385162178))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1350725169) (.branch 47 (.leaf 1317293675) (.leaf 1284831490))) (.branch 50 (.branch 49 (.leaf 1253304003) (.leaf 1222678115)) (.branch 51 (.leaf 1192922160) (.leaf 1164005837)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1135900137) (.leaf 1108577281)) (.branch 55 (.leaf 1082010657) (.leaf 1056174765))) (.branch 58 (.branch 57 (.leaf 1031045158) (.leaf 1006598396)) (.branch 59 (.leaf 982811993) (.leaf 959664372))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 937134825) (.branch 62 (.leaf 915203466) (.leaf 893851197))) (.branch 65 (.branch 64 (.leaf 873059668) (.leaf 852811245)) (.branch 66 (.leaf 833088974) (.leaf 813876551)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 795158292) (.leaf 776919106)) (.branch 70 (.leaf 759144467) (.leaf 741820388))) (.branch 73 (.branch 72 (.leaf 724933399) (.leaf 708470523)) (.branch 74 (.leaf 692419255) (.leaf 676767538))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 661503751) (.branch 77 (.leaf 646616681) (.leaf 632095514))) (.branch 80 (.branch 79 (.leaf 617929811) (.leaf 604109498)) (.branch 81 (.leaf 590624845) (.leaf 577466458)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 564625259) (.leaf 552092477)) (.branch 85 (.leaf 539859635) (.leaf 527918535))) (.branch 88 (.branch 87 (.leaf 516261250) (.leaf 504880114)) (.branch 89 (.leaf 493767708) (.leaf 482916852)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 472320596) (.branch 92 (.leaf 461972212) (.leaf 451865182))) (.branch 95 (.branch 94 (.leaf 441993193) (.leaf 432350129)) (.branch 96 (.leaf 422930062) (.leaf 413727247)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 404736113) (.leaf 395951256)) (.branch 100 (.leaf 387367438) (.leaf 378979574))) (.branch 103 (.branch 102 (.leaf 370782731) (.leaf 362772123)) (.branch 104 (.leaf 354943101) (.leaf 347291152))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 339811895) (.leaf 332501074)) (.branch 108 (.leaf 325354554) (.leaf 318368316))) (.branch 111 (.branch 110 (.leaf 311538457) (.leaf 304861182)) (.branch 112 (.leaf 298332802) (.leaf 291949728)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 285708474) (.leaf 279605645)) (.branch 116 (.leaf 273637942) (.leaf 267802153))) (.branch 119 (.branch 118 (.leaf 262095153) (.leaf 256513902)) (.branch 120 (.leaf 251055439) (.leaf 245716881)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 814).prefactor = (4690762485900927/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 814).cutoff/(generalMeanRows 814).c)).2 =
    (362984702278429/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 814).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 814).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 814).q*(generalMeanRows 814).c/2-2 = (829/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable068.value]
    have hcontinuation : (generalMeanRows 814).q*(generalMeanRows 814).cutoff/2-2 = (15670/7581:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable265.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 814).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 814

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 814).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 814).criticalRate j.val*(generalMeanRows 814).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 814).c*(generalMeanRows 814).criticalPoint j.val)).2-
      (generalMeanRows 814).J/2-(generalMeanRows 814).error (generalMeanGrid j.val)+
      (generalMeanRows 814).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 814).c)).2-
      (generalMeanRows 814).J/2-(generalMeanRows 814).error 4 := by
  have he : (generalMeanRows 814).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 814) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 814)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0814

/-! Kernel-checked entropy margins for general spectral rectangle 815. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0815
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4934465338) (.branch 2 (.leaf 4763877002) (.leaf 4600856010))) (.branch 5 (.branch 4 (.leaf 4444976673) (.leaf 4295843144)) (.branch 6 (.leaf 4153086816) (.leaf 4016363995)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3885353830) (.leaf 3759756440)) (.branch 10 (.leaf 3639291243) (.leaf 3523695442))) (.branch 13 (.branch 12 (.leaf 3412722651) (.leaf 3306141666)) (.branch 14 (.leaf 3203735326) (.leaf 3105299498))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3010642136) (.branch 17 (.leaf 2919582428) (.leaf 2831950016))) (.branch 20 (.branch 19 (.leaf 2747584273) (.leaf 2666333651)) (.branch 21 (.leaf 2588055072) (.leaf 2512613370)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2439880776) (.leaf 2369736444)) (.branch 25 (.leaf 2302066010) (.leaf 2236761188))) (.branch 28 (.branch 27 (.leaf 2173719389) (.leaf 2112843372)) (.branch 29 (.leaf 2054040921) (.leaf 1997224542)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1942311180) (.branch 32 (.leaf 1889221960) (.leaf 1837881941))) (.branch 35 (.branch 34 (.leaf 1788219886) (.leaf 1740168056)) (.branch 36 (.leaf 1693662005) (.leaf 1648640395)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1605044824) (.leaf 1562819666)) (.branch 40 (.leaf 1521911909) (.leaf 1482271022))) (.branch 43 (.branch 42 (.leaf 1443848815) (.leaf 1406599316)) (.branch 44 (.leaf 1370478650) (.leaf 1335444928))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1301458148) (.branch 47 (.leaf 1268480087) (.leaf 1236474217))) (.branch 50 (.branch 49 (.leaf 1205405613) (.leaf 1175240875)) (.branch 51 (.leaf 1145948046) (.leaf 1117496541)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1089857079) (.leaf 1063001620)) (.branch 55 (.leaf 1036903297) (.leaf 1011536366))) (.branch 58 (.branch 57 (.leaf 986876146) (.leaf 962898970)) (.branch 59 (.leaf 939582134) (.leaf 916903854))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 894843220) (.branch 62 (.leaf 873380154) (.leaf 852495373))) (.branch 65 (.branch 64 (.leaf 832170350) (.leaf 812387282)) (.branch 66 (.leaf 793129053) (.leaf 774379203)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 756121901) (.leaf 738341914)) (.branch 70 (.leaf 721024581) (.leaf 704155788))) (.branch 73 (.branch 72 (.leaf 687721941) (.leaf 671709947)) (.branch 74 (.leaf 656107191) (.leaf 640901513))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 626081189) (.branch 77 (.leaf 611634915) (.leaf 597551787))) (.branch 80 (.branch 79 (.leaf 583821281) (.leaf 570433246)) (.branch 81 (.leaf 557377876) (.leaf 544645708)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 532227598) (.leaf 520114713)) (.branch 85 (.leaf 508298519) (.leaf 496770766))) (.branch 88 (.branch 87 (.leaf 485523476) (.leaf 474548938)) (.branch 89 (.leaf 463839689) (.leaf 453388511)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 443188418) (.branch 92 (.leaf 433232650) (.leaf 423514658))) (.branch 95 (.branch 94 (.leaf 414028105) (.leaf 404766848)) (.branch 96 (.leaf 395724941) (.leaf 386896618)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 378276293) (.leaf 369858549)) (.branch 100 (.leaf 361638135) (.leaf 353609959))) (.branch 103 (.branch 102 (.leaf 345769080) (.leaf 338110706)) (.branch 104 (.leaf 330630187) (.leaf 323323009))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 316184791) (.leaf 309211278)) (.branch 108 (.leaf 302398340) (.leaf 295741965))) (.branch 111 (.branch 110 (.leaf 289238256) (.leaf 282883427)) (.branch 112 (.leaf 276673797) (.leaf 270605792)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 264675935) (.leaf 258880846)) (.branch 116 (.leaf 253217241) (.leaf 247681923))) (.branch 119 (.branch 118 (.leaf 242271785) (.leaf 236983803)) (.branch 120 (.leaf 231815036) (.leaf 226762622)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 815).prefactor = (1173737882378287/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 815).cutoff/(generalMeanRows 815).c)).2 =
    (88249550203013/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 815).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 815).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 815).q*(generalMeanRows 815).c/2-2 = (1699/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable222.value]
    have hcontinuation : (generalMeanRows 815).q*(generalMeanRows 815).cutoff/2-2 = (7814/3801:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable261.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 815).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 815

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 815).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 815).criticalRate j.val*(generalMeanRows 815).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 815).c*(generalMeanRows 815).criticalPoint j.val)).2-
      (generalMeanRows 815).J/2-(generalMeanRows 815).error (generalMeanGrid j.val)+
      (generalMeanRows 815).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 815).c)).2-
      (generalMeanRows 815).J/2-(generalMeanRows 815).error 4 := by
  have he : (generalMeanRows 815).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 815) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 815)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0815

/-! Kernel-checked entropy margins for general spectral rectangle 816. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0816
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4952001092) (.branch 2 (.leaf 4780806531) (.leaf 4617206207))) (.branch 5 (.branch 4 (.leaf 4460772917) (.leaf 4311109408)) (.branch 6 (.leaf 4167845762) (.leaf 4030637065)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3899161325) (.leaf 3773117596)) (.branch 10 (.leaf 3652224299) (.leaf 3536217701))) (.branch 13 (.branch 12 (.leaf 3424850544) (.leaf 3317890798)) (.branch 14 (.leaf 3215120534) (.leaf 3116334892))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3021341143) (.branch 17 (.leaf 2929957834) (.leaf 2842013999))) (.branch 20 (.branch 19 (.leaf 2757348443) (.leaf 2675809079)) (.branch 21 (.leaf 2597252319) (.leaf 2521542518)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2448551451) (.leaf 2378157845)) (.branch 25 (.leaf 2310246930) (.leaf 2244710032))) (.branch 28 (.branch 27 (.leaf 2181444199) (.leaf 2120351845)) (.branch 29 (.leaf 2061340426) (.leaf 2004322137)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1949213628) (.branch 32 (.leaf 1895935744) (.leaf 1844413276))) (.branch 35 (.branch 34 (.leaf 1794574736) (.leaf 1746352143)) (.branch 36 (.leaf 1699680821) (.leaf 1654499216)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1610748719) (.leaf 1568373504)) (.branch 40 (.leaf 1527320372) (.leaf 1487538612))) (.branch 43 (.branch 42 (.leaf 1448979863) (.leaf 1411597989)) (.branch 44 (.leaf 1375348960) (.leaf 1340190738))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1306083177) (.branch 47 (.leaf 1272987921) (.leaf 1240868311))) (.branch 50 (.branch 49 (.leaf 1209689298) (.leaf 1179417363)) (.branch 51 (.leaf 1150020435) (.leaf 1121467821)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1093730136) (.leaf 1066779240)) (.branch 55 (.leaf 1040588171) (.leaf 1015131092))) (.branch 58 (.branch 57 (.leaf 990383237) (.leaf 966320852)) (.branch 59 (.leaf 942921154) (.leaf 920162282))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 898023250) (.branch 62 (.leaf 876483910) (.leaf 855524910))) (.branch 65 (.branch 64 (.leaf 835127658) (.leaf 815274287)) (.branch 66 (.leaf 795947619) (.leaf 777131137)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 758808954) (.leaf 740965781)) (.branch 70 (.leaf 723586907) (.leaf 706658167))) (.branch 73 (.branch 72 (.leaf 690165918) (.leaf 674097023)) (.branch 74 (.leaf 658438819) (.leaf 643179103))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 628306112) (.branch 77 (.leaf 613808500) (.leaf 599675324))) (.branch 80 (.branch 79 (.leaf 585896024) (.leaf 572460411)) (.branch 81 (.leaf 559358646) (.leaf 546581231)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 534118990) (.leaf 521963060)) (.branch 85 (.leaf 510104875) (.leaf 498536155))) (.branch 88 (.branch 87 (.leaf 487248895) (.leaf 476235356)) (.branch 89 (.leaf 465488049) (.leaf 454999731)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 444763390) (.branch 92 (.leaf 434772241) (.leaf 425019715))) (.branch 95 (.branch 94 (.leaf 415499448) (.leaf 406205280)) (.branch 96 (.leaf 397131240) (.leaf 388271544)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 379620584) (.leaf 371172926)) (.branch 100 (.leaf 362923299) (.leaf 354866593))) (.branch 103 (.branch 102 (.leaf 346997850) (.leaf 339312260)) (.branch 104 (.leaf 331805157) (.leaf 324472012))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 317308426) (.leaf 310310131)) (.branch 108 (.leaf 303472982) (.leaf 296792952))) (.branch 111 (.branch 110 (.leaf 290266131) (.leaf 283888718)) (.branch 112 (.leaf 277657021) (.leaf 271567452)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 265616521) (.leaf 259800839)) (.branch 116 (.leaf 254117106) (.leaf 248562118))) (.branch 119 (.branch 118 (.leaf 243132753) (.leaf 237825980)) (.branch 120 (.leaf 232638844) (.leaf 227568475)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 816).prefactor = (2355818058017747/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 816).cutoff/(generalMeanRows 816).c)).2 =
    (88249550203013/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 816).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 816).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 816).q*(generalMeanRows 816).c/2-2 = (1699/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable222.value]
    have hcontinuation : (generalMeanRows 816).q*(generalMeanRows 816).cutoff/2-2 = (7814/3801:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable261.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 816).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 816

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 816).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 816).criticalRate j.val*(generalMeanRows 816).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 816).c*(generalMeanRows 816).criticalPoint j.val)).2-
      (generalMeanRows 816).J/2-(generalMeanRows 816).error (generalMeanGrid j.val)+
      (generalMeanRows 816).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 816).c)).2-
      (generalMeanRows 816).J/2-(generalMeanRows 816).error 4 := by
  have he : (generalMeanRows 816).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 816) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 816)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0816

/-! Kernel-checked entropy margins for general spectral rectangle 817. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0817
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5258974505) (.branch 2 (.leaf 5091710673) (.leaf 4931707128))) (.branch 5 (.branch 4 (.leaf 4778552583) (.leaf 4631864811)) (.branch 6 (.leaf 4491288110) (.leaf 4356491028)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4227164343) (.leaf 4103019237)) (.branch 10 (.leaf 3983785663) (.leaf 3869210864))) (.branch 13 (.branch 12 (.leaf 3759058041) (.leaf 3653105138)) (.branch 14 (.leaf 3551143744) (.leaf 3452978093))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3358424146) (.branch 17 (.leaf 3267308763) (.leaf 3179468933))) (.branch 20 (.branch 19 (.leaf 3094751079) (.leaf 3013010411)) (.branch 21 (.leaf 2934110336) (.leaf 2857921914)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2784323356) (.leaf 2713199557)) (.branch 25 (.leaf 2644441672) (.leaf 2577946716))) (.branch 28 (.branch 27 (.leaf 2513617196) (.leaf 2451360773)) (.branch 29 (.leaf 2391089942) (.leaf 2332721740)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2276177469) (.branch 32 (.leaf 2221382446) (.leaf 2168265762))) (.branch 35 (.branch 34 (.leaf 2116760060) (.leaf 2066801330)) (.branch 36 (.leaf 2018328718) (.leaf 1971284339)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1925613116) (.leaf 1881262614)) (.branch 40 (.leaf 1838182901) (.leaf 1796326401))) (.branch 43 (.branch 42 (.leaf 1755647771) (.leaf 1716103773)) (.branch 44 (.leaf 1677653164) (.leaf 1640256588))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1603876472) (.branch 47 (.leaf 1568476935) (.leaf 1534023696))) (.branch 50 (.branch 49 (.leaf 1500483993) (.leaf 1467826499)) (.branch 51 (.leaf 1436021254) (.leaf 1405039589)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1374854065) (.leaf 1345438406)) (.branch 55 (.leaf 1316767444) (.leaf 1288817062))) (.branch 58 (.branch 57 (.leaf 1261564142) (.leaf 1234986514)) (.branch 59 (.leaf 1209062914) (.leaf 1183772934))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1159096984) (.branch 62 (.leaf 1135016252) (.leaf 1111512666))) (.branch 65 (.branch 64 (.leaf 1088568860) (.leaf 1066168140)) (.branch 66 (.leaf 1044294453) (.leaf 1022932354)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1002066984) (.leaf 981684036)) (.branch 70 (.leaf 961769736) (.leaf 942310814))) (.branch 73 (.branch 72 (.leaf 923294484) (.leaf 904708421)) (.branch 74 (.leaf 886540742) (.leaf 868779984))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 851415089) (.branch 77 (.leaf 834435381) (.leaf 817830556))) (.branch 80 (.branch 79 (.leaf 801590662) (.leaf 785706084)) (.branch 81 (.leaf 770167531) (.leaf 754966020)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 740092868) (.leaf 725539674)) (.branch 85 (.leaf 711298312) (.leaf 697360915))) (.branch 88 (.branch 87 (.leaf 683719870) (.leaf 670367802)) (.branch 89 (.leaf 657297569) (.leaf 644502251)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 631975140) (.branch 92 (.leaf 619709736) (.leaf 607699734))) (.branch 95 (.branch 94 (.leaf 595939017) (.leaf 584421653)) (.branch 96 (.leaf 573141884) (.leaf 562094121)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 551272938) (.leaf 540673065)) (.branch 100 (.leaf 530289382) (.leaf 520116915))) (.branch 103 (.branch 102 (.leaf 510150830) (.leaf 500386427)) (.branch 104 (.leaf 490819139) (.leaf 481444521))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 472258250) (.leaf 463256123)) (.branch 108 (.leaf 454434047) (.leaf 445788038))) (.branch 111 (.branch 110 (.leaf 437314219) (.leaf 429008813)) (.branch 112 (.leaf 420868145) (.leaf 412888632)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 405066783) (.leaf 397399199)) (.branch 116 (.leaf 389882565) (.leaf 382513649))) (.branch 119 (.branch 118 (.leaf 375289303) (.leaf 368206454)) (.branch 120 (.leaf 361262107) (.leaf 354453340)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 817).prefactor = (2286118069730219/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 817).cutoff/(generalMeanRows 817).c)).2 =
    (80157050254481/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 817).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 817).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 817).q*(generalMeanRows 817).c/2-2 = (587/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable263.value]
    have hcontinuation : (generalMeanRows 817).q*(generalMeanRows 817).cutoff/2-2 = (7766/3731:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable262.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 817).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 817

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 817).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 817).criticalRate j.val*(generalMeanRows 817).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 817).c*(generalMeanRows 817).criticalPoint j.val)).2-
      (generalMeanRows 817).J/2-(generalMeanRows 817).error (generalMeanGrid j.val)+
      (generalMeanRows 817).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 817).c)).2-
      (generalMeanRows 817).J/2-(generalMeanRows 817).error 4 := by
  have he : (generalMeanRows 817).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 817) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 817)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0817

/-! Kernel-checked entropy margins for general spectral rectangle 818. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0818
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5124194276) (.branch 2 (.leaf 4956462192) (.leaf 4796062451))) (.branch 5 (.branch 4 (.leaf 4642580509) (.leaf 4495631053)) (.branch 6 (.leaf 4354855453) (.leaf 4219919475)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4090511247) (.leaf 3966339431)) (.branch 10 (.leaf 3847131571) (.leaf 3732632614))) (.branch 13 (.branch 12 (.leaf 3622603563) (.leaf 3516820260)) (.branch 14 (.leaf 3415072282) (.leaf 3317161933))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3222903324) (.branch 17 (.leaf 3132121539) (.leaf 3044651861))) (.branch 20 (.branch 19 (.leaf 2960339074) (.leaf 2879036811)) (.branch 21 (.leaf 2800606963) (.leaf 2724919130)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2651850118) (.leaf 2581283469)) (.branch 25 (.leaf 2513109033) (.leaf 2447222566))) (.branch 28 (.branch 27 (.leaf 2383525366) (.leaf 2321923922)) (.branch 29 (.leaf 2262329602) (.leaf 2204658355)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2148830434) (.branch 32 (.leaf 2094770140) (.leaf 2042405588))) (.branch 35 (.branch 34 (.leaf 1991668475) (.leaf 1942493880)) (.branch 36 (.leaf 1894820067) (.leaf 1848588303)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1803742687) (.leaf 1760229994)) (.branch 40 (.leaf 1717999524) (.leaf 1677002963))) (.branch 43 (.branch 42 (.leaf 1637194253) (.leaf 1598529467)) (.branch 44 (.leaf 1560966697) (.leaf 1524465942))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1488989010) (.branch 47 (.leaf 1454499420) (.leaf 1420962315))) (.branch 50 (.branch 49 (.leaf 1388344371) (.leaf 1356613726)) (.branch 51 (.leaf 1325739898) (.leaf 1295693719)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1266447264) (.leaf 1237973792)) (.branch 55 (.leaf 1210247685) (.leaf 1183244393))) (.branch 58 (.branch 57 (.leaf 1156940380) (.leaf 1131313074)) (.branch 59 (.leaf 1106340822) (.leaf 1082002843))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1058279189) (.branch 62 (.leaf 1035150700) (.leaf 1012598973))) (.branch 65 (.branch 64 (.leaf 990606321) (.leaf 969155741)) (.branch 66 (.leaf 948230885) (.leaf 927816024)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 907896025) (.leaf 888456320)) (.branch 70 (.leaf 869482882) (.leaf 850962201))) (.branch 73 (.branch 72 (.leaf 832881258) (.leaf 815227507)) (.branch 74 (.leaf 797988853) (.leaf 781153629))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 764710583) (.branch 77 (.leaf 748648854) (.leaf 732957959))) (.branch 80 (.branch 79 (.leaf 717627776) (.leaf 702648529)) (.branch 81 (.leaf 688010773) (.leaf 673705379)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 659723523) (.leaf 646056671)) (.branch 85 (.leaf 632696571) (.leaf 619635237))) (.branch 88 (.branch 87 (.leaf 606864942) (.leaf 594378203)) (.branch 89 (.leaf 582167777) (.leaf 570226649)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 558548022) (.branch 92 (.leaf 547125307) (.leaf 535952121))) (.branch 95 (.branch 94 (.leaf 525022275) (.leaf 514329764)) (.branch 96 (.leaf 503868766) (.leaf 493633631)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 483618877) (.leaf 473819182)) (.branch 100 (.leaf 464229378) (.leaf 454844448))) (.branch 103 (.branch 102 (.leaf 445659517) (.leaf 436669850)) (.branch 104 (.leaf 427870845) (.leaf 419258029))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 410827054) (.leaf 402573693)) (.branch 108 (.leaf 394493833) (.leaf 386583476))) (.branch 111 (.branch 110 (.leaf 378838728) (.leaf 371255805)) (.branch 112 (.leaf 363831020) (.leaf 356560786)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 349441611) (.leaf 342470092)) (.branch 116 (.leaf 335642917) (.leaf 328956860))) (.branch 119 (.branch 118 (.leaf 322408776) (.leaf 315995603)) (.branch 120 (.leaf 309714354) (.leaf 303562119)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 818).prefactor = (184165334187283/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 818).cutoff/(generalMeanRows 818).c)).2 =
    (386079103882709/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 818).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 818).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 818).q*(generalMeanRows 818).c/2-2 = (3097/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable249.value]
    have hcontinuation : (generalMeanRows 818).q*(generalMeanRows 818).cutoff/2-2 = (7766/3731:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable262.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 818).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 818

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 818).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 818).criticalRate j.val*(generalMeanRows 818).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 818).c*(generalMeanRows 818).criticalPoint j.val)).2-
      (generalMeanRows 818).J/2-(generalMeanRows 818).error (generalMeanGrid j.val)+
      (generalMeanRows 818).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 818).c)).2-
      (generalMeanRows 818).J/2-(generalMeanRows 818).error 4 := by
  have he : (generalMeanRows 818).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 818) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 818)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0818

/-! Kernel-checked entropy margins for general spectral rectangle 819. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0819
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5169217093) (.branch 2 (.leaf 5002367191) (.leaf 4842809580))) (.branch 5 (.branch 4 (.leaf 4690129814) (.leaf 4543942778)) (.branch 6 (.leaf 4403890120) (.leaf 4269637968)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4140874882) (.leaf 4017310017)) (.branch 10 (.leaf 3898671471) (.leaf 3784704788))) (.branch 13 (.branch 12 (.leaf 3675171617) (.leaf 3569848483)) (.branch 14 (.leaf 3468525678) (.leaf 3371006248))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3277105074) (.branch 17 (.leaf 3186648024) (.leaf 3099471186))) (.branch 20 (.branch 19 (.leaf 3015420158) (.leaf 2934349398)) (.branch 21 (.leaf 2856121628) (.leaf 2780607285)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2707684007) (.leaf 2637236176)) (.branch 25 (.leaf 2569154472) (.leaf 2503335484))) (.branch 28 (.branch 27 (.leaf 2439681328) (.leaf 2378099313)) (.branch 29 (.leaf 2318501611) (.leaf 2260804969)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2204930427) (.branch 32 (.leaf 2150803061) (.leaf 2098351746))) (.branch 35 (.branch 34 (.leaf 2047508931) (.leaf 1998210431)) (.branch 36 (.leaf 1950395229) (.leaf 1904005301)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1858985437) (.leaf 1815283090)) (.branch 40 (.leaf 1772848221) (.leaf 1731633163))) (.branch 43 (.branch 42 (.leaf 1691592487) (.leaf 1652682882)) (.branch 44 (.leaf 1614863038) (.leaf 1578093539))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1542336760) (.branch 47 (.leaf 1507556773) (.leaf 1473719256))) (.branch 50 (.branch 49 (.leaf 1440791409) (.leaf 1408741874)) (.branch 51 (.leaf 1377540663) (.leaf 1347159083)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1317569672) (.leaf 1288746137)) (.branch 55 (.leaf 1260663294) (.leaf 1233297012))) (.branch 58 (.branch 57 (.leaf 1206624162) (.leaf 1180622566)) (.branch 59 (.leaf 1155270949) (.leaf 1130548900))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1106436822) (.branch 62 (.leaf 1082915902) (.leaf 1059968064))) (.branch 65 (.branch 64 (.leaf 1037575941) (.leaf 1015722839)) (.branch 66 (.leaf 994392704) (.leaf 973570095)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 953240151) (.leaf 933388571)) (.branch 70 (.leaf 914001582) (.leaf 895065919))) (.branch 73 (.branch 72 (.leaf 876568799) (.leaf 858497902)) (.branch 74 (.leaf 840841350) (.leaf 823587686))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 806725855) (.branch 77 (.leaf 790245191) (.leaf 774135395))) (.branch 80 (.branch 79 (.leaf 758386521) (.leaf 742988961)) (.branch 81 (.leaf 727933431) (.leaf 713210959)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 698812867) (.leaf 684730763)) (.branch 85 (.leaf 670956530) (.leaf 657482310))) (.branch 88 (.branch 87 (.leaf 644300498) (.leaf 631403730)) (.branch 89 (.leaf 618784873) (.leaf 606437018)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 594353467) (.branch 92 (.leaf 582527730) (.leaf 570953513))) (.branch 95 (.branch 94 (.leaf 559624711) (.leaf 548535404)) (.branch 96 (.leaf 537679845) (.leaf 527052458)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 516647828) (.leaf 506460699)) (.branch 100 (.leaf 496485964) (.leaf 486718662))) (.branch 103 (.branch 102 (.leaf 477153972) (.leaf 467787210)) (.branch 104 (.leaf 458613822) (.leaf 449629377))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 440829568) (.leaf 432210207)) (.branch 108 (.leaf 423767215) (.leaf 415496626))) (.branch 111 (.branch 110 (.leaf 407394577) (.leaf 399457310)) (.branch 112 (.leaf 391681163) (.leaf 384062572)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 376598064) (.leaf 369284255)) (.branch 116 (.leaf 362117849) (.leaf 355095633))) (.branch 119 (.branch 118 (.leaf 348214475) (.leaf 341471322)) (.branch 120 (.leaf 334863196) (.leaf 328387196)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 819).prefactor = (2298073853629751/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 819).cutoff/(generalMeanRows 819).c)).2 =
    (1595659199143/4000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 819).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 819).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 819).q*(generalMeanRows 819).c/2-2 = (377/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable247.value]
    have hcontinuation : (generalMeanRows 819).q*(generalMeanRows 819).cutoff/2-2 = (15614/7421:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable266.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 819).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 819

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 819).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 819).criticalRate j.val*(generalMeanRows 819).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 819).c*(generalMeanRows 819).criticalPoint j.val)).2-
      (generalMeanRows 819).J/2-(generalMeanRows 819).error (generalMeanGrid j.val)+
      (generalMeanRows 819).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 819).c)).2-
      (generalMeanRows 819).J/2-(generalMeanRows 819).error 4 := by
  have he : (generalMeanRows 819).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 819) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 819)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0819

/-! Kernel-checked entropy margins for general spectral rectangle 820. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0820
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5119546725) (.branch 2 (.leaf 4951917035) (.leaf 4791640225))) (.branch 5 (.branch 4 (.leaf 4638298805) (.leaf 4491504800)) (.branch 6 (.leaf 4350897171) (.leaf 4216139513)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4086917998) (.leaf 3962939525)) (.branch 10 (.leaf 3843930058) (.leaf 3729633126))) (.branch 13 (.branch 12 (.leaf 3619808461) (.leaf 3514230775)) (.branch 14 (.leaf 3412688635) (.leaf 3314983450))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3220928543) (.branch 17 (.leaf 3130348300) (.leaf 3043077394))) (.branch 20 (.branch 19 (.leaf 2958960075) (.leaf 2877849518)) (.branch 21 (.leaf 2799607218) (.leaf 2724102436)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2651211695) (.leaf 2580818301)) (.branch 25 (.leaf 2512811912) (.leaf 2447088134))) (.branch 28 (.branch 27 (.leaf 2383548145) (.leaf 2322098352)) (.branch 29 (.leaf 2262650065) (.leaf 2205119204)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2149426015) (.branch 32 (.leaf 2095494813) (.leaf 2043253743))) (.branch 35 (.branch 34 (.leaf 1992634553) (.leaf 1943572383)) (.branch 36 (.leaf 1896005571) (.leaf 1849875470)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1805126275) (.leaf 1761704864)) (.branch 40 (.leaf 1719560648) (.leaf 1678645428))) (.branch 43 (.branch 42 (.leaf 1638913267) (.leaf 1600320363)) (.branch 44 (.leaf 1562824936) (.leaf 1526387116))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1490968842) (.branch 47 (.leaf 1456533767) (.leaf 1423047166))) (.branch 50 (.branch 49 (.leaf 1390475850) (.leaf 1358788091)) (.branch 51 (.leaf 1327953538) (.leaf 1297943155)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1268729147) (.leaf 1240284903)) (.branch 55 (.leaf 1212584929) (.leaf 1185604802))) (.branch 58 (.branch 57 (.leaf 1159321105) (.leaf 1133711389)) (.branch 59 (.leaf 1108754117) (.leaf 1084428622))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1060715067) (.branch 62 (.leaf 1037594404) (.leaf 1015048334))) (.branch 65 (.branch 64 (.leaf 993059273) (.leaf 971610320)) (.branch 66 (.leaf 950685223) (.leaf 930268348)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 910344654) (.leaf 890899660)) (.branch 70 (.leaf 871919427) (.leaf 853390525))) (.branch 73 (.branch 72 (.leaf 835300018) (.leaf 817635437)) (.branch 74 (.leaf 800384758) (.leaf 783536390))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 767079147) (.branch 77 (.leaf 751002236) (.leaf 735295238))) (.branch 80 (.branch 79 (.leaf 719948092) (.leaf 704951081)) (.branch 81 (.leaf 690294816) (.leaf 675970223)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 661968530) (.leaf 648281253)) (.branch 85 (.leaf 634900187) (.leaf 621817392))) (.branch 88 (.branch 87 (.leaf 609025184) (.leaf 596516123)) (.branch 89 (.leaf 584283005) (.leaf 572318853)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 560616904) (.branch 92 (.leaf 549170608) (.leaf 537973612))) (.branch 95 (.branch 94 (.leaf 527019757) (.leaf 516303070)) (.branch 96 (.leaf 505817757) (.leaf 495558194)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 485518925) (.leaf 475694651)) (.branch 100 (.leaf 466080227) (.leaf 456670658))) (.branch 103 (.branch 102 (.leaf 447461089) (.leaf 438446805)) (.branch 104 (.leaf 429623221) (.leaf 420985882))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 412530456) (.leaf 404252731)) (.branch 108 (.leaf 396148608) (.leaf 388214101))) (.branch 111 (.branch 110 (.leaf 380445332) (.leaf 372838526)) (.branch 112 (.leaf 365390007) (.leaf 358096199)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 350953618) (.leaf 343958873)) (.branch 116 (.leaf 337108657) (.leaf 330399752))) (.branch 119 (.branch 118 (.leaf 323829021) (.leaf 317393406)) (.branch 120 (.leaf 311089929) (.leaf 304915685)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 820).prefactor = (1156918908217309/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 820).cutoff/(generalMeanRows 820).c)).2 =
    (391588759693677/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 820).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 820).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 820).q*(generalMeanRows 820).c/2-2 = (3097/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable249.value]
    have hcontinuation : (generalMeanRows 820).q*(generalMeanRows 820).cutoff/2-2 = (15614/7421:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable266.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 820).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 820

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 820).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 820).criticalRate j.val*(generalMeanRows 820).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 820).c*(generalMeanRows 820).criticalPoint j.val)).2-
      (generalMeanRows 820).J/2-(generalMeanRows 820).error (generalMeanGrid j.val)+
      (generalMeanRows 820).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 820).c)).2-
      (generalMeanRows 820).J/2-(generalMeanRows 820).error 4 := by
  have he : (generalMeanRows 820).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 820) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 820)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0820

/-! Kernel-checked entropy margins for general spectral rectangle 821. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0821
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5076315066) (.branch 2 (.leaf 4907814596) (.leaf 4746707727))) (.branch 5 (.branch 4 (.leaf 4592576790) (.leaf 4445033540)) (.branch 6 (.leaf 4303716584) (.leaf 4168289093)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4038436744) (.leaf 3913865886)) (.branch 10 (.leaf 3794301876) (.leaf 3679487591))) (.branch 13 (.branch 12 (.leaf 3569182075) (.leaf 3463159311)) (.branch 14 (.leaf 3361207110) (.leaf 3263126100))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3168728800) (.branch 17 (.leaf 3077838774) (.leaf 2990289865))) (.branch 20 (.branch 19 (.leaf 2905925476) (.leaf 2824597932)) (.branch 21 (.leaf 2746167869) (.leaf 2670503693)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2597481068) (.leaf 2526982444)) (.branch 25 (.leaf 2458896628) (.leaf 2393118379))) (.branch 28 (.branch 27 (.leaf 2329548038) (.leaf 2268091181)) (.branch 29 (.leaf 2208658301) (.leaf 2151164506)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2095529245) (.branch 32 (.leaf 2041676051) (.leaf 1989532296))) (.branch 35 (.branch 34 (.leaf 1939028971) (.leaf 1890100474)) (.branch 36 (.leaf 1842684417) (.leaf 1796721440)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1752155041) (.leaf 1708931417)) (.branch 40 (.leaf 1666999316) (.leaf 1626309889))) (.branch 43 (.branch 42 (.leaf 1586816568) (.leaf 1548474935)) (.branch 44 (.leaf 1511242609) (.leaf 1475079138))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1439945893) (.branch 47 (.leaf 1405805976) (.leaf 1372624125))) (.branch 50 (.branch 49 (.leaf 1340366634) (.leaf 1309001267)) (.branch 51 (.leaf 1278497187) (.leaf 1248824882)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1219956099) (.leaf 1191863781)) (.branch 55 (.leaf 1164522007) (.leaf 1137905933))) (.branch 58 (.branch 57 (.leaf 1111991745) (.leaf 1086756601)) (.branch 59 (.leaf 1062178591) (.leaf 1038236685))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1014910696) (.branch 62 (.leaf 992181238) (.leaf 970029686))) (.branch 65 (.branch 64 (.leaf 948438145) (.leaf 927389411)) (.branch 66 (.leaf 906866940) (.leaf 886854819)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 867337737) (.leaf 848300956)) (.branch 70 (.leaf 829730286) (.leaf 811612060))) (.branch 73 (.branch 72 (.leaf 793933111) (.leaf 776680750)) (.branch 74 (.leaf 759842743) (.leaf 743407295))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 727363027) (.branch 77 (.leaf 711698959) (.leaf 696404495))) (.branch 80 (.branch 79 (.leaf 681469405) (.leaf 666883807)) (.branch 81 (.leaf 652638157) (.leaf 638723234)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 625130123) (.leaf 611850206)) (.branch 85 (.leaf 598875149) (.leaf 586196889))) (.branch 88 (.branch 87 (.leaf 573807625) (.leaf 561699807)) (.branch 89 (.leaf 549866126) (.leaf 538299504)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 526993085) (.branch 92 (.leaf 515940227) (.leaf 505134493))) (.branch 95 (.branch 94 (.leaf 494569645) (.leaf 484239633)) (.branch 96 (.leaf 474138591) (.leaf 464260829)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 454600827) (.leaf 445153227)) (.branch 100 (.leaf 435912830) (.leaf 426874586))) (.branch 103 (.branch 102 (.leaf 418033594) (.leaf 409385093)) (.branch 104 (.leaf 400924456) (.leaf 392647190))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 384548927) (.leaf 376625420)) (.branch 108 (.leaf 368872543) (.leaf 361286281))) (.branch 111 (.branch 110 (.leaf 353862731) (.leaf 346598094)) (.branch 112 (.leaf 339488677) (.leaf 332530884)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 325721216) (.leaf 319056266)) (.branch 116 (.leaf 312532719) (.leaf 306147346))) (.branch 119 (.branch 118 (.leaf 299897000) (.leaf 293778620)) (.branch 120 (.leaf 287789221) (.leaf 281925896)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 821).prefactor = (927250618783551/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 821).cutoff/(generalMeanRows 821).c)).2 =
    (37880634455363/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 821).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 821).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 821).q*(generalMeanRows 821).c/2-2 = (1589/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable251.value]
    have hcontinuation : (generalMeanRows 821).q*(generalMeanRows 821).cutoff/2-2 = (7766/3731:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable262.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 821).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 821

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 821).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 821).criticalRate j.val*(generalMeanRows 821).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 821).c*(generalMeanRows 821).criticalPoint j.val)).2-
      (generalMeanRows 821).J/2-(generalMeanRows 821).error (generalMeanGrid j.val)+
      (generalMeanRows 821).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 821).c)).2-
      (generalMeanRows 821).J/2-(generalMeanRows 821).error 4 := by
  have he : (generalMeanRows 821).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 821) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 821)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0821

/-! Kernel-checked entropy margins for general spectral rectangle 822. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0822
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5029279326) (.branch 2 (.leaf 4860039422) (.leaf 4698254393))) (.branch 5 (.branch 4 (.leaf 4543503397) (.leaf 4395395210)) (.branch 6 (.leaf 4253565642) (.leaf 4117675225)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3987407152) (.leaf 3862465423)) (.branch 10 (.leaf 3742573181) (.leaf 3627471204))) (.branch 13 (.branch 12 (.leaf 3516916548) (.leaf 3410681312)) (.branch 14 (.leaf 3308551521) (.leaf 3210326106))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3115815970) (.branch 17 (.leaf 3024843145) (.leaf 2937240011))) (.branch 20 (.branch 19 (.leaf 2852848582) (.leaf 2771519854)) (.branch 21 (.leaf 2693113201) (.leaf 2617495822)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2544542227) (.leaf 2474133768)) (.branch 25 (.leaf 2406158198) (.leaf 2340509273))) (.branch 28 (.branch 27 (.leaf 2277086372) (.leaf 2215794150)) (.branch 29 (.leaf 2156542221) (.leaf 2099244850)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2043820679) (.branch 32 (.leaf 1990192468) (.leaf 1938286847))) (.branch 35 (.branch 34 (.leaf 1888034099) (.leaf 1839367941)) (.branch 36 (.leaf 1792225331) (.leaf 1746546284)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1702273699) (.leaf 1659353196)) (.branch 40 (.leaf 1617732971) (.leaf 1577363646))) (.branch 43 (.branch 42 (.leaf 1538198144) (.leaf 1500191560)) (.branch 44 (.leaf 1463301044) (.leaf 1427485694))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1392706451) (.branch 47 (.leaf 1358926002) (.leaf 1326108691))) (.branch 50 (.branch 49 (.leaf 1294220426) (.leaf 1263228609)) (.branch 51 (.leaf 1233102051) (.leaf 1203810902)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1175326588) (.leaf 1147621740)) (.branch 55 (.leaf 1120670140) (.leaf 1094446660))) (.branch 58 (.branch 57 (.leaf 1068927210) (.leaf 1044088689)) (.branch 59 (.leaf 1019908931) (.leaf 996366669))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 973441483) (.branch 62 (.leaf 951113766) (.leaf 929364681))) (.branch 65 (.branch 64 (.leaf 908176130) (.leaf 887530712)) (.branch 66 (.leaf 867411701) (.leaf 847803003)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 828689137) (.leaf 810055203)) (.branch 70 (.leaf 791886855) (.leaf 774170276))) (.branch 73 (.branch 72 (.leaf 756892158) (.leaf 740039676)) (.branch 74 (.leaf 723600467) (.leaf 707562611))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 691914613) (.branch 77 (.leaf 676645381) (.leaf 661744210))) (.branch 80 (.branch 79 (.leaf 647200770) (.leaf 633005082)) (.branch 81 (.leaf 619147512) (.leaf 605618749)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 592409798) (.leaf 579511960)) (.branch 85 (.leaf 566916829) (.leaf 554616271))) (.branch 88 (.branch 87 (.leaf 542602420) (.leaf 530867662)) (.branch 89 (.leaf 519404629) (.leaf 508206188)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 497265432) (.branch 92 (.leaf 486575668) (.leaf 476130415))) (.branch 95 (.branch 94 (.leaf 465923392) (.leaf 455948508)) (.branch 96 (.leaf 446199862) (.leaf 436671727)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 427358553) (.leaf 418254952)) (.branch 100 (.leaf 409355698) (.leaf 400655717))) (.branch 103 (.branch 102 (.leaf 392150085) (.leaf 383834020)) (.branch 104 (.leaf 375702879) (.leaf 367752150))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 359977451) (.leaf 352374525)) (.branch 108 (.leaf 344939232) (.leaf 337667549))) (.branch 111 (.branch 110 (.leaf 330555566) (.leaf 323599478)) (.branch 112 (.leaf 316795587) (.leaf 310140295)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 303630099) (.leaf 297261595)) (.branch 116 (.leaf 291031466) (.leaf 284936485))) (.branch 119 (.branch 118 (.leaf 278973512) (.leaf 273139486)) (.branch 120 (.leaf 267431429) (.leaf 261846441)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 822).prefactor = (933719381911613/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 822).cutoff/(generalMeanRows 822).c)).2 =
    (185793048290071/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 822).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 822).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 822).q*(generalMeanRows 822).c/2-2 = (3259/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable253.value]
    have hcontinuation : (generalMeanRows 822).q*(generalMeanRows 822).cutoff/2-2 = (7766/3731:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable262.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 822).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 822

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 822).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 822).criticalRate j.val*(generalMeanRows 822).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 822).c*(generalMeanRows 822).criticalPoint j.val)).2-
      (generalMeanRows 822).J/2-(generalMeanRows 822).error (generalMeanGrid j.val)+
      (generalMeanRows 822).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 822).c)).2-
      (generalMeanRows 822).J/2-(generalMeanRows 822).error 4 := by
  have he : (generalMeanRows 822).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 822) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 822)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0822

/-! Kernel-checked entropy margins for general spectral rectangle 823. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0823
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5080940282) (.branch 2 (.leaf 4912365862) (.leaf 4751162827))) (.branch 5 (.branch 4 (.leaf 4596916518) (.leaf 4449241415)) (.branch 6 (.leaf 4307778595) (.leaf 4172193461)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4042173708) (.leaf 3917427502)) (.branch 10 (.leaf 3797681843) (.leaf 3682681080))) (.branch 13 (.branch 12 (.leaf 3572185580) (.leaf 3465970511)) (.branch 14 (.leaf 3363824745) (.leaf 3265549854))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3170959195) (.branch 17 (.leaf 3079877077) (.leaf 2992137996))) (.branch 20 (.branch 19 (.leaf 2907585932) (.leaf 2826073712)) (.branch 21 (.leaf 2747462410) (.leaf 2671620808)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2598424889) (.leaf 2527757377)) (.branch 25 (.leaf 2459507304) (.leaf 2393569615))) (.branch 28 (.branch 27 (.leaf 2329844799) (.leaf 2268238548)) (.branch 29 (.leaf 2208661439) (.leaf 2151028637)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2095259627) (.branch 32 (.leaf 2041277951) (.leaf 1989010976))) (.branch 35 (.branch 34 (.leaf 1938389665) (.leaf 1889348379)) (.branch 36 (.leaf 1841824672) (.leaf 1795759119)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1751095144) (.leaf 1707778857)) (.branch 40 (.leaf 1665758911) (.leaf 1624986360))) (.branch 43 (.branch 42 (.leaf 1585414529) (.leaf 1546998888)) (.branch 44 (.leaf 1509696944) (.leaf 1473468127))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1438273687) (.branch 47 (.leaf 1404076605) (.leaf 1370841497))) (.branch 50 (.branch 49 (.leaf 1338534532) (.leaf 1307123352)) (.branch 51 (.leaf 1276576995) (.leaf 1246865826)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1217961471) (.leaf 1189836751)) (.branch 55 (.leaf 1162465625) (.leaf 1135823134))) (.branch 58 (.branch 57 (.leaf 1109885344) (.leaf 1084629302)) (.branch 59 (.leaf 1060032984) (.leaf 1036075251))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1012735811) (.branch 62 (.leaf 989995170) (.leaf 967834604))) (.branch 65 (.branch 64 (.leaf 946236115) (.leaf 925182404)) (.branch 66 (.leaf 904656833) (.leaf 884643398)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 865126697) (.leaf 846091908)) (.branch 70 (.leaf 827524756) (.leaf 809411494))) (.branch 73 (.branch 72 (.leaf 791738877) (.leaf 774494139)) (.branch 74 (.leaf 757664976) (.leaf 741239521))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 725206326) (.branch 77 (.leaf 709554348) (.leaf 694272927))) (.branch 80 (.branch 79 (.leaf 679351771) (.leaf 664780942)) (.branch 81 (.leaf 650550841) (.leaf 636652190)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 623076024) (.leaf 609813677)) (.branch 85 (.leaf 596856765) (.leaf 584197182))) (.branch 88 (.branch 87 (.leaf 571827083) (.leaf 559738876)) (.branch 89 (.leaf 547925213) (.leaf 536378977)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 525093276) (.branch 92 (.leaf 514061434) (.leaf 503276982))) (.branch 95 (.branch 94 (.leaf 492733648) (.leaf 482425355)) (.branch 96 (.leaf 472346207) (.leaf 462490488)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 452852652) (.leaf 443427316)) (.branch 100 (.leaf 434209257) (.leaf 425193407))) (.branch 103 (.branch 102 (.leaf 416374841) (.leaf 407748778)) (.branch 104 (.leaf 399310575) (.leaf 391055720))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 382979828) (.leaf 375078638)) (.branch 108 (.leaf 367348008) (.leaf 359783910))) (.branch 111 (.branch 110 (.leaf 352382428) (.leaf 345139752)) (.branch 112 (.leaf 338052175) (.leaf 331116093)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324327995) (.leaf 317684468)) (.branch 116 (.leaf 311182185) (.leaf 304817909))) (.branch 119 (.branch 118 (.leaf 298588490) (.leaf 292490855)) (.branch 120 (.leaf 286522016) (.leaf 280679058)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 823).prefactor = (4612255327749571/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 823).cutoff/(generalMeanRows 823).c)).2 =
    (93331719697251/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 823).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 823).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 823).q*(generalMeanRows 823).c/2-2 = (1589/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable251.value]
    have hcontinuation : (generalMeanRows 823).q*(generalMeanRows 823).cutoff/2-2 = (5150/2501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable264.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 823).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 823

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 823).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 823).criticalRate j.val*(generalMeanRows 823).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 823).c*(generalMeanRows 823).criticalPoint j.val)).2-
      (generalMeanRows 823).J/2-(generalMeanRows 823).error (generalMeanGrid j.val)+
      (generalMeanRows 823).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 823).c)).2-
      (generalMeanRows 823).J/2-(generalMeanRows 823).error 4 := by
  have he : (generalMeanRows 823).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 823) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 823)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0823

/-! Kernel-checked entropy margins for general spectral rectangle 824. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0824
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5034835328) (.branch 2 (.leaf 4865501940) (.leaf 4703601872))) (.branch 5 (.branch 4 (.leaf 4548717260) (.leaf 4400459573)) (.branch 6 (.leaf 4258467060) (.leaf 4122402458)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3991950950) (.leaf 3866818332)) (.branch 10 (.leaf 3746729363) (.leaf 3631426273))) (.branch 13 (.branch 12 (.leaf 3520667420) (.leaf 3414226072)) (.branch 14 (.leaf 3311889294) (.leaf 3213456942))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3118740746) (.branch 17 (.leaf 3027563463) (.leaf 2939758116))) (.branch 20 (.branch 19 (.leaf 2855167280) (.leaf 2773642441)) (.branch 21 (.leaf 2695043399) (.leaf 2619237715)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2546100211) (.leaf 2475512500)) (.branch 25 (.leaf 2407362553) (.leaf 2341544301))) (.branch 28 (.branch 27 (.leaf 2277957262) (.leaf 2216506199)) (.branch 29 (.leaf 2157100802) (.leaf 2099655386)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2044088622) (.branch 32 (.leaf 1990323271) (.leaf 1938285952))) (.branch 35 (.branch 34 (.leaf 1887906915) (.leaf 1839119832)) (.branch 36 (.leaf 1791861600) (.leaf 1746072163)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1701694339) (.leaf 1658673659)) (.branch 40 (.leaf 1616958218) (.leaf 1576498537))) (.branch 43 (.branch 42 (.leaf 1537247426) (.leaf 1499159866)) (.branch 44 (.leaf 1462192891) (.leaf 1426305477))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1391458441) (.branch 47 (.leaf 1357614346) (.leaf 1324737408))) (.branch 50 (.branch 49 (.leaf 1292793412) (.leaf 1261749630)) (.branch 51 (.leaf 1231574747) (.leaf 1202238790)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1173713057) (.leaf 1145970058)) (.branch 55 (.leaf 1118983452) (.leaf 1092727991))) (.branch 58 (.branch 57 (.leaf 1067179468) (.leaf 1042314663)) (.branch 59 (.leaf 1018111299) (.leaf 994547995))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 971604225) (.branch 62 (.leaf 949260272) (.leaf 927497199))) (.branch 65 (.branch 64 (.leaf 906296802) (.leaf 885641587)) (.branch 66 (.leaf 865514728) (.leaf 845900040)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 826781951) (.leaf 808145473)) (.branch 70 (.leaf 789976176) (.leaf 772260161))) (.branch 73 (.branch 72 (.leaf 754984041) (.leaf 738134912)) (.branch 74 (.leaf 721700340) (.leaf 705668333))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 690027324) (.branch 77 (.leaf 674766158) (.leaf 659874065))) (.branch 80 (.branch 79 (.leaf 645340653) (.leaf 631155885)) (.branch 81 (.leaf 617310069) (.leaf 603793840)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 590598149) (.leaf 577714250)) (.branch 85 (.leaf 565133686) (.leaf 552848278))) (.branch 88 (.branch 87 (.leaf 540850114) (.leaf 529131541)) (.branch 89 (.leaf 517685148) (.leaf 506503765)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 495580445) (.branch 92 (.leaf 484908464) (.leaf 474481305))) (.branch 95 (.branch 94 (.leaf 464292655) (.leaf 454336393)) (.branch 96 (.leaf 444606588) (.leaf 435097487)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 425803512) (.leaf 416719252)) (.branch 100 (.leaf 407839455) (.leaf 399159026))) (.branch 103 (.branch 102 (.leaf 390673020) (.leaf 382376634)) (.branch 104 (.leaf 374265205) (.leaf 366334206))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 358579235) (.leaf 350996020)) (.branch 108 (.leaf 343580407) (.leaf 336328358))) (.branch 111 (.branch 110 (.leaf 329235948) (.leaf 322299361)) (.branch 112 (.leaf 315514887) (.leaf 308878917)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 302387938) (.leaf 296038534)) (.branch 116 (.leaf 289827382) (.leaf 283751246))) (.branch 119 (.branch 118 (.leaf 277806976) (.leaf 271991507)) (.branch 120 (.leaf 266301852) (.leaf 260735105)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 824).prefactor = (4644986203944291/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 824).cutoff/(generalMeanRows 824).c)).2 =
    (183053315407759/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 824).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 824).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 824).q*(generalMeanRows 824).c/2-2 = (3259/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable253.value]
    have hcontinuation : (generalMeanRows 824).q*(generalMeanRows 824).cutoff/2-2 = (5150/2501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable264.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 824).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 824

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 824).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 824).criticalRate j.val*(generalMeanRows 824).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 824).c*(generalMeanRows 824).criticalPoint j.val)).2-
      (generalMeanRows 824).J/2-(generalMeanRows 824).error (generalMeanGrid j.val)+
      (generalMeanRows 824).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 824).c)).2-
      (generalMeanRows 824).J/2-(generalMeanRows 824).error 4 := by
  have he : (generalMeanRows 824).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 824) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 824)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0824

/-! Kernel-checked entropy margins for general spectral rectangle 825. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0825
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4995085911) (.branch 2 (.leaf 4824955621) (.leaf 4662297389))) (.branch 5 (.branch 4 (.leaf 4506693133) (.leaf 4357754028)) (.branch 6 (.leaf 4215117949) (.leaf 4078447196)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3947426454) (.leaf 3821760967)) (.branch 10 (.leaf 3701174895) (.leaf 3585409827))) (.branch 13 (.branch 12 (.leaf 3474223445) (.leaf 3367388307)) (.branch 14 (.leaf 3264690741) (.leaf 3165929847))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3070916573) (.branch 17 (.leaf 2979472887) (.leaf 2891431002))) (.branch 20 (.branch 19 (.leaf 2806632683) (.leaf 2724928593)) (.branch 21 (.leaf 2646177707) (.leaf 2570246762)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2497009754) (.leaf 2426347474)) (.branch 25 (.leaf 2358147075) (.leaf 2292301674))) (.branch 28 (.branch 27 (.leaf 2228709987) (.leaf 2167275981)) (.branch 29 (.leaf 2107908558) (.leaf 2050521258)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1995031987) (.branch 32 (.leaf 1941362757) (.leaf 1889439446))) (.branch 35 (.branch 34 (.leaf 1839191581) (.leaf 1790552120)) (.branch 36 (.leaf 1743457267) (.leaf 1697846284)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1653661322) (.leaf 1610847262)) (.branch 40 (.leaf 1569351563) (.leaf 1529124125))) (.branch 43 (.branch 42 (.leaf 1490117158) (.leaf 1452285052)) (.branch 44 (.leaf 1415584269) (.leaf 1379973228))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1345412206) (.branch 47 (.leaf 1311863239) (.leaf 1279290034))) (.branch 50 (.branch 49 (.leaf 1247657879) (.leaf 1216933569)) (.branch 51 (.leaf 1187085321) (.leaf 1158082713)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1129896606) (.leaf 1102499089)) (.branch 55 (.leaf 1075863411) (.leaf 1049963931))) (.branch 58 (.branch 57 (.leaf 1024776060) (.leaf 1000276212)) (.branch 59 (.leaf 976441753) (.leaf 953250961))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 930682977) (.branch 62 (.leaf 908717770) (.leaf 887336093))) (.branch 65 (.branch 64 (.leaf 866519450) (.leaf 846250060)) (.branch 66 (.leaf 826510826) (.leaf 807285301)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 788557661) (.leaf 770312675)) (.branch 70 (.leaf 752535681) (.leaf 735212557))) (.branch 73 (.branch 72 (.leaf 718329704) (.leaf 701874013)) (.branch 74 (.leaf 685832853) (.leaf 670194045))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 654945845) (.branch 77 (.leaf 640076923) (.leaf 625576349))) (.branch 80 (.branch 79 (.leaf 611433573) (.leaf 597638410)) (.branch 81 (.leaf 584181026) (.leaf 571051920)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 558241916) (.leaf 545742145)) (.branch 85 (.leaf 533544033) (.leaf 521639292))) (.branch 88 (.branch 87 (.leaf 510019907) (.leaf 498678123)) (.branch 89 (.leaf 487606439) (.leaf 476797593)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 466244558) (.branch 92 (.leaf 455940528) (.leaf 445878915))) (.branch 95 (.branch 94 (.leaf 436053333) (.leaf 426457600)) (.branch 96 (.leaf 417085722) (.leaf 407931888)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 398990469) (.leaf 390256002)) (.branch 100 (.leaf 381723191) (.leaf 373386897))) (.branch 103 (.branch 102 (.leaf 365242136) (.leaf 357284070)) (.branch 104 (.leaf 349508003) (.leaf 341909376))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 334483762) (.leaf 327226863)) (.branch 108 (.leaf 320134502) (.leaf 313202624))) (.branch 111 (.branch 110 (.leaf 306427286) (.leaf 299804657)) (.branch 112 (.leaf 293331014) (.leaf 287002736)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 280816304) (.leaf 274768295)) (.branch 116 (.leaf 268855381) (.leaf 263074321))) (.branch 119 (.branch 118 (.leaf 257421966) (.leaf 251895250)) (.branch 120 (.leaf 246491189) (.leaf 241206879)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 825).prefactor = (4653891647809653/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 825).cutoff/(generalMeanRows 825).c)).2 =
    (353488536569337/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 825).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 825).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 825).q*(generalMeanRows 825).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 825).q*(generalMeanRows 825).cutoff/2-2 = (1921/943:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable260.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 825).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 825

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 825).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 825).criticalRate j.val*(generalMeanRows 825).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 825).c*(generalMeanRows 825).criticalPoint j.val)).2-
      (generalMeanRows 825).J/2-(generalMeanRows 825).error (generalMeanGrid j.val)+
      (generalMeanRows 825).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 825).c)).2-
      (generalMeanRows 825).J/2-(generalMeanRows 825).error 4 := by
  have he : (generalMeanRows 825).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 825) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 825)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0825

/-! Kernel-checked entropy margins for general spectral rectangle 826. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0826
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4951527183) (.branch 2 (.leaf 4780672012) (.leaf 4617351517))) (.branch 5 (.branch 4 (.leaf 4461144279) (.leaf 4311658343)) (.branch 6 (.leaf 4168528644) (.leaf 4031414712)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3899998626) (.leaf 3773983169)) (.branch 10 (.leaf 3653090175) (.leaf 3537059036))) (.branch 13 (.branch 12 (.leaf 3425645356) (.leaf 3318619720)) (.branch 14 (.leaf 3215766590) (.leaf 3116883293))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3021779095) (.branch 17 (.leaf 2930274363) (.leaf 2842199792))) (.branch 20 (.branch 19 (.leaf 2757395696) (.leaf 2675711365)) (.branch 21 (.leaf 2597004458) (.leaf 2521140465)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2447992187) (.leaf 2377439278)) (.branch 25 (.leaf 2309367805) (.leaf 2243669851))) (.branch 28 (.branch 27 (.leaf 2180243141) (.leaf 2118990695)) (.branch 29 (.leaf 2059820514) (.leaf 2002645274)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1947382054) (.branch 32 (.leaf 1893952077) (.leaf 1842280467))) (.branch 35 (.branch 34 (.leaf 1792296025) (.leaf 1743931021)) (.branch 36 (.leaf 1697120995) (.leaf 1651804576)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1607923308) (.leaf 1565421493)) (.branch 40 (.leaf 1524246033) (.leaf 1484346297))) (.branch 43 (.branch 42 (.leaf 1445673982) (.leaf 1408182994)) (.branch 44 (.leaf 1371829326) (.leaf 1336570950))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1302367713) (.branch 47 (.leaf 1269181243) (.leaf 1236974852))) (.branch 50 (.branch 49 (.leaf 1205713455) (.leaf 1175363482)) (.branch 51 (.leaf 1145892811) (.leaf 1117270685)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1089467654) (.leaf 1062455501)) (.branch 55 (.leaf 1036207189) (.leaf 1010696799))) (.branch 58 (.branch 57 (.leaf 985899479) (.leaf 961791389)) (.branch 59 (.leaf 938349655) (.leaf 915552323))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 893378315) (.branch 62 (.leaf 871807387) (.leaf 850820093))) (.branch 65 (.branch 64 (.leaf 830397745) (.leaf 810522379)) (.branch 66 (.leaf 791176723) (.leaf 772344165)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 754008720) (.leaf 736155008)) (.branch 70 (.leaf 718768223) (.leaf 701834108))) (.branch 73 (.branch 72 (.leaf 685338930) (.leaf 669269460)) (.branch 74 (.leaf 653612949) (.leaf 638357107))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 623490083) (.branch 77 (.leaf 609000450) (.leaf 594877182))) (.branch 80 (.branch 79 (.leaf 581109638) (.leaf 567687551)) (.branch 81 (.leaf 554601006) (.leaf 541840428)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 529396570) (.leaf 517260496)) (.branch 85 (.leaf 505423570) (.leaf 493877446))) (.branch 88 (.branch 87 (.leaf 482614054) (.leaf 471625587)) (.branch 89 (.leaf 460904498) (.leaf 450443480)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 440235466) (.branch 92 (.leaf 430273611) (.leaf 420551293))) (.branch 95 (.branch 94 (.leaf 411062094) (.leaf 401799801)) (.branch 96 (.leaf 392758395) (.leaf 383932041)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 375315088) (.leaf 366902053)) (.branch 100 (.leaf 358687623) (.leaf 350666646))) (.branch 103 (.branch 102 (.leaf 342834123) (.leaf 335185206)) (.branch 104 (.leaf 327715189) (.leaf 320419506))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 313293726) (.leaf 306333546)) (.branch 108 (.leaf 299534787) (.leaf 292893393))) (.branch 111 (.branch 110 (.leaf 286405422) (.leaf 280067045)) (.branch 112 (.leaf 273874543) (.leaf 267824300)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 261912802) (.leaf 256136634)) (.branch 116 (.leaf 250492474) (.leaf 244977094))) (.branch 119 (.branch 118 (.leaf 239587353) (.leaf 234320197)) (.branch 120 (.leaf 229172653) (.leaf 224141831)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 826).prefactor = (585936878256543/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 826).cutoff/(generalMeanRows 826).c)).2 =
    (86592767200119/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 826).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 826).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 826).q*(generalMeanRows 826).c/2-2 = (3421/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable252.value]
    have hcontinuation : (generalMeanRows 826).q*(generalMeanRows 826).cutoff/2-2 = (1921/943:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable260.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 826).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 826

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 826).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 826).criticalRate j.val*(generalMeanRows 826).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 826).c*(generalMeanRows 826).criticalPoint j.val)).2-
      (generalMeanRows 826).J/2-(generalMeanRows 826).error (generalMeanGrid j.val)+
      (generalMeanRows 826).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 826).c)).2-
      (generalMeanRows 826).J/2-(generalMeanRows 826).error 4 := by
  have he : (generalMeanRows 826).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 826) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 826)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0826

/-! Kernel-checked entropy margins for general spectral rectangle 827. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0827
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4989545308) (.branch 2 (.leaf 4819480734) (.leaf 4656911419))) (.branch 5 (.branch 4 (.leaf 4501416244) (.leaf 4352603627)) (.branch 6 (.leaf 4210108944) (.leaf 4073592231)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3942736124) (.leaf 3817244016)) (.branch 10 (.leaf 3696838393) (.leaf 3581259340))) (.branch 13 (.branch 12 (.leaf 3470263181) (.leaf 3363621256)) (.branch 14 (.leaf 3261118802) (.leaf 3162553942))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3067736755) (.branch 17 (.leaf 2976488434) (.leaf 2888640508))) (.branch 20 (.branch 19 (.leaf 2804034135) (.leaf 2722519449)) (.branch 21 (.leaf 2643954959) (.leaf 2568207001)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2495149222) (.leaf 2424662116)) (.branch 25 (.leaf 2356632585) (.leaf 2290953540))) (.branch 28 (.branch 27 (.leaf 2227523524) (.leaf 2166246367)) (.branch 29 (.leaf 2107030865) (.leaf 2049790482)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1994443070) (.branch 32 (.leaf 1940910611) (.leaf 1889118975))) (.branch 35 (.branch 34 (.leaf 1838997695) (.leaf 1790479755)) (.branch 36 (.leaf 1743501398) (.leaf 1698001938)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1653923587) (.leaf 1611211299)) (.branch 40 (.leaf 1569812616) (.leaf 1529677525))) (.branch 43 (.branch 42 (.leaf 1490758330) (.leaf 1453009523)) (.branch 44 (.leaf 1416387669) (.leaf 1380851296))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1346360792) (.branch 47 (.leaf 1312878307) (.leaf 1280367661))) (.branch 50 (.branch 49 (.leaf 1248794262) (.leaf 1218125019)) (.branch 51 (.leaf 1188328268) (.leaf 1159373703)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1131232303) (.leaf 1103876271)) (.branch 55 (.leaf 1077278973) (.leaf 1051414881))) (.branch 58 (.branch 57 (.leaf 1026259518) (.leaf 1001789407)) (.branch 59 (.leaf 977982024) (.leaf 954815753))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 932269841) (.branch 62 (.leaf 910324356) (.leaf 888960153))) (.branch 65 (.branch 64 (.leaf 868158834) (.leaf 847902711)) (.branch 66 (.leaf 828174782) (.leaf 808958687)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 790238692) (.leaf 771999651)) (.branch 70 (.leaf 754226983) (.leaf 736906649))) (.branch 73 (.branch 72 (.leaf 720025123) (.leaf 703569375)) (.branch 74 (.leaf 687526844) (.leaf 671885422))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 656633433) (.branch 77 (.leaf 641759612) (.leaf 627253091))) (.branch 80 (.branch 79 (.leaf 613103382) (.leaf 599300358)) (.branch 81 (.leaf 585834240) (.leaf 572695583)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 559875262) (.leaf 547364458)) (.branch 85 (.leaf 535154645) (.leaf 523237581))) (.branch 88 (.branch 87 (.leaf 511605294) (.leaf 500250072)) (.branch 89 (.leaf 489164455) (.leaf 478341219)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 467773373) (.branch 92 (.leaf 457454149) (.leaf 447376990))) (.branch 95 (.branch 94 (.leaf 437535545) (.leaf 427923660)) (.branch 96 (.leaf 418535371) (.leaf 409364897)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 400406632) (.leaf 391655141)) (.branch 100 (.leaf 383105151) (.leaf 374751547))) (.branch 103 (.branch 102 (.leaf 366589366) (.leaf 358613789)) (.branch 104 (.leaf 350820141) (.leaf 343203882))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 335760602) (.leaf 328486019)) (.branch 108 (.leaf 321375972) (.leaf 314426421))) (.branch 111 (.branch 110 (.leaf 307633436) (.leaf 300993200)) (.branch 112 (.leaf 294502001) (.leaf 288156232)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 281952382) (.leaf 275887040)) (.branch 116 (.leaf 269956886) (.leaf 264158691))) (.branch 119 (.branch 118 (.leaf 258489311) (.leaf 252945688)) (.branch 120 (.leaf 247524847) (.leaf 242223889)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 827).prefactor = (935589870969271/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 827).cutoff/(generalMeanRows 827).c)).2 =
    (44867267667113/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 827).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 827).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 827).q*(generalMeanRows 827).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 827).q*(generalMeanRows 827).cutoff/2-2 = (5150/2501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable264.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 827).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 827

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 827).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 827).criticalRate j.val*(generalMeanRows 827).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 827).c*(generalMeanRows 827).criticalPoint j.val)).2-
      (generalMeanRows 827).J/2-(generalMeanRows 827).error (generalMeanGrid j.val)+
      (generalMeanRows 827).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 827).c)).2-
      (generalMeanRows 827).J/2-(generalMeanRows 827).error 4 := by
  have he : (generalMeanRows 827).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 827) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 827)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0827

/-! Kernel-checked entropy margins for general spectral rectangle 828. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0828
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4866819579) (.branch 2 (.leaf 4696580917) (.leaf 4533907604))) (.branch 5 (.branch 4 (.leaf 4378374893) (.leaf 4229587768)) (.branch 6 (.leaf 4087178358) (.leaf 3950803619)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3820143264) (.leaf 3694897909)) (.branch 10 (.leaf 3574787400) (.leaf 3459549306))) (.branch 13 (.branch 12 (.leaf 3348937557) (.leaf 3242721210)) (.branch 14 (.leaf 3140683322) (.leaf 3042619937))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2948339146) (.branch 17 (.leaf 2857660241) (.leaf 2770412936))) (.branch 20 (.branch 19 (.leaf 2686436649) (.leaf 2605579851)) (.branch 21 (.leaf 2527699458) (.leaf 2452660277)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2380334496) (.leaf 2310601206)) (.branch 25 (.leaf 2243345965) (.leaf 2178460395))) (.branch 28 (.branch 27 (.leaf 2115841803) (.leaf 2055392835)) (.branch 29 (.leaf 1997021150) (.leaf 1940639120)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1886163553) (.branch 32 (.leaf 1833515424) (.leaf 1782619640))) (.branch 35 (.branch 34 (.leaf 1733404811) (.leaf 1685803034)) (.branch 36 (.leaf 1639749700) (.leaf 1595183306)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1552045284) (.leaf 1510279834)) (.branch 40 (.leaf 1469833778) (.leaf 1430656413))) (.branch 43 (.branch 42 (.leaf 1392699380) (.leaf 1355916537)) (.branch 44 (.leaf 1320263840) (.leaf 1285699234))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1252182548) (.branch 47 (.leaf 1219675399) (.leaf 1188141094))) (.branch 50 (.branch 49 (.leaf 1157544551) (.leaf 1127852209)) (.branch 51 (.leaf 1099031958) (.leaf 1071053062)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1043886090) (.leaf 1017502855)) (.branch 55 (.leaf 991876349) (.leaf 966980687))) (.branch 58 (.branch 57 (.leaf 942791052) (.leaf 919283644)) (.branch 59 (.leaf 896435629) (.leaf 874225098))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 852631017) (.branch 62 (.leaf 831633190) (.leaf 811212218))) (.branch 65 (.branch 64 (.leaf 791349463) (.leaf 772027011)) (.branch 66 (.leaf 753227642) (.leaf 734934796)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 717132543) (.leaf 699805555)) (.branch 70 (.leaf 682939081) (.leaf 666518919))) (.branch 73 (.branch 72 (.leaf 650531390) (.leaf 634963322)) (.branch 74 (.leaf 619802021) (.leaf 605035252))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 590651222) (.branch 77 (.leaf 576638558) (.leaf 562986290))) (.branch 80 (.branch 79 (.leaf 549683835) (.leaf 536720979)) (.branch 81 (.leaf 524087865) (.leaf 511774973)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 499773111) (.leaf 488073399)) (.branch 85 (.leaf 476667257) (.leaf 465546393))) (.branch 88 (.branch 87 (.leaf 454702791) (.leaf 444128700)) (.branch 89 (.leaf 433816626) (.leaf 423759318)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 413949760) (.branch 92 (.leaf 404381163) (.leaf 395046955))) (.branch 95 (.branch 94 (.leaf 385940775) (.leaf 377056460)) (.branch 96 (.leaf 368388044) (.leaf 359929744)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351675959) (.leaf 343621261)) (.branch 100 (.leaf 335760386) (.leaf 328088231))) (.branch 103 (.branch 102 (.leaf 320599850) (.leaf 313290444)) (.branch 104 (.leaf 306155357) (.leaf 299190073))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 292390210) (.leaf 285751512)) (.branch 108 (.leaf 279269851) (.leaf 272941218))) (.branch 111 (.branch 110 (.leaf 266761719) (.leaf 260727572)) (.branch 112 (.leaf 254835106) (.leaf 249080751)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 243461040) (.leaf 237972604)) (.branch 116 (.leaf 232612168) (.leaf 227376548))) (.branch 119 (.branch 118 (.leaf 222262649) (.leaf 217267461)) (.branch 120 (.leaf 212388057) (.leaf 207621590)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 828).prefactor = (2355573214396773/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 828).cutoff/(generalMeanRows 828).c)).2 =
    (344753506344949/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 828).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 828).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 828).q*(generalMeanRows 828).c/2-2 = (1751/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable267.value]
    have hcontinuation : (generalMeanRows 828).q*(generalMeanRows 828).cutoff/2-2 = (5150/2501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable264.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 828).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 828

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 828).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 828).criticalRate j.val*(generalMeanRows 828).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 828).c*(generalMeanRows 828).criticalPoint j.val)).2-
      (generalMeanRows 828).J/2-(generalMeanRows 828).error (generalMeanGrid j.val)+
      (generalMeanRows 828).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 828).c)).2-
      (generalMeanRows 828).J/2-(generalMeanRows 828).error 4 := by
  have he : (generalMeanRows 828).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 828) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 828)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0828

/-! Kernel-checked entropy margins for general spectral rectangle 829. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0829
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5290737174) (.branch 2 (.leaf 5123862793) (.leaf 4964199710))) (.branch 5 (.branch 4 (.leaf 4811339785) (.leaf 4664903730)) (.branch 6 (.leaf 4524538584) (.leaf 4389915464)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4260727550) (.leaf 4136688276)) (.branch 10 (.leaf 4017529707) (.leaf 3903001069))) (.branch 13 (.branch 12 (.leaf 3792867424) (.leaf 3686908466)) (.branch 14 (.leaf 3584917431) (.leaf 3486700100))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3392073893) (.branch 17 (.leaf 3300867042) (.leaf 3212917829))) (.branch 20 (.branch 19 (.leaf 3128073895) (.leaf 3046191601)) (.branch 21 (.leaf 2967135435) (.leaf 2890777480)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2816996909) (.leaf 2745679529)) (.branch 25 (.leaf 2676717352) (.leaf 2610008202))) (.branch 28 (.branch 27 (.leaf 2545455353) (.leaf 2482967184)) (.branch 29 (.leaf 2422456873) (.leaf 2363842099)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2307044773) (.branch 32 (.leaf 2251990782) (.leaf 2198609759))) (.branch 35 (.branch 34 (.leaf 2146834858) (.leaf 2096602549)) (.branch 36 (.leaf 2047852433) (.leaf 2000527053)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1954571736) (.leaf 1909934431)) (.branch 40 (.leaf 1866565561) (.leaf 1824417892))) (.branch 43 (.branch 42 (.leaf 1783446397) (.leaf 1743608142)) (.branch 44 (.leaf 1704862165) (.leaf 1667169377))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1630492455) (.branch 47 (.leaf 1594795754) (.leaf 1560045216))) (.branch 50 (.branch 49 (.leaf 1526208284) (.leaf 1493253829)) (.branch 51 (.leaf 1461152073) (.leaf 1429874520)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1399393891) (.leaf 1369684062)) (.branch 55 (.leaf 1340720004) (.leaf 1312477734))) (.branch 58 (.branch 57 (.leaf 1284934255) (.leaf 1258067515)) (.branch 59 (.leaf 1231856352) (.leaf 1206280462))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1181320344) (.branch 62 (.leaf 1156957274) (.leaf 1133173258))) (.branch 65 (.branch 64 (.leaf 1109951005) (.leaf 1087273887)) (.branch 66 (.leaf 1065125913) (.leaf 1043491697)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1022356430) (.leaf 1001705854)) (.branch 70 (.leaf 981526239) (.leaf 961804353))) (.branch 73 (.branch 72 (.leaf 942527445) (.leaf 923683224)) (.branch 74 (.leaf 905259833) (.leaf 887245836))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 869630194) (.branch 77 (.leaf 852402253) (.leaf 835551724))) (.branch 80 (.branch 79 (.leaf 819068668) (.leaf 802943481)) (.branch 81 (.leaf 787166882) (.leaf 771729894)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 756623838) (.leaf 741840317)) (.branch 85 (.leaf 727371204) (.leaf 713208633))) (.branch 88 (.branch 87 (.leaf 699344986) (.leaf 685772885)) (.branch 89 (.leaf 672485183) (.leaf 659474953)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 646735479) (.branch 92 (.leaf 634260251) (.leaf 622042953))) (.branch 95 (.branch 94 (.leaf 610077458) (.leaf 598357821)) (.branch 96 (.leaf 586878271) (.leaf 575633205)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564617181) (.leaf 553824914)) (.branch 100 (.leaf 543251267) (.leaf 532891251))) (.branch 103 (.branch 102 (.leaf 522740013) (.leaf 512792835)) (.branch 104 (.leaf 503045132) (.leaf 493492439))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 484130416) (.leaf 474954837)) (.branch 108 (.leaf 465961591) (.leaf 457146673))) (.branch 111 (.branch 110 (.leaf 448506186) (.leaf 440036333)) (.branch 112 (.leaf 431733415) (.leaf 423593829)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 415614064) (.leaf 407790698)) (.branch 116 (.leaf 400120393) (.leaf 392599899))) (.branch 119 (.branch 118 (.leaf 385226042) (.leaf 377995730)) (.branch 120 (.leaf 370905944) (.leaf 363953741)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 829).prefactor = (456914611581671/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 829).cutoff/(generalMeanRows 829).c)).2 =
    (50437369643/125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 829).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 829).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 829).q*(generalMeanRows 829).c/2-2 = (73/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable024.value]
    have hcontinuation : (generalMeanRows 829).q*(generalMeanRows 829).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 829).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 829

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 829).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 829).criticalRate j.val*(generalMeanRows 829).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 829).c*(generalMeanRows 829).criticalPoint j.val)).2-
      (generalMeanRows 829).J/2-(generalMeanRows 829).error (generalMeanGrid j.val)+
      (generalMeanRows 829).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 829).c)).2-
      (generalMeanRows 829).J/2-(generalMeanRows 829).error 4 := by
  have he : (generalMeanRows 829).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 829) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 829)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0829

/-! Kernel-checked entropy margins for general spectral rectangle 830. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0830
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5240736811) (.branch 2 (.leaf 5073020191) (.leaf 4912576334))) (.branch 5 (.branch 4 (.leaf 4758994071) (.leaf 4611891270)) (.branch 6 (.leaf 4470912294) (.leaf 4335725740)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4206022410) (.leaf 4081513492)) (.branch 10 (.leaf 3961928926) (.leaf 3847015927))) (.branch 13 (.branch 12 (.leaf 3736537650) (.leaf 3630271980)) (.branch 14 (.leaf 3528010433) (.leaf 3429557155))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3334728012) (.branch 17 (.leaf 3243349755) (.leaf 3155259254))) (.branch 20 (.branch 19 (.leaf 3070302803) (.leaf 2988335476)) (.branch 21 (.leaf 2909220535) (.leaf 2832828889)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2759038590) (.leaf 2687734368)) (.branch 25 (.leaf 2618807208) (.leaf 2552153950))) (.branch 28 (.branch 27 (.leaf 2487676922) (.leaf 2425283601)) (.branch 29 (.leaf 2364886295) (.leaf 2306401851)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2249751380) (.branch 32 (.leaf 2194860003) (.leaf 2141656614))) (.branch 35 (.branch 34 (.leaf 2090073659) (.leaf 2040046929)) (.branch 36 (.leaf 1991515367) (.leaf 1944420891)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1898708221) (.leaf 1854324722)) (.branch 40 (.leaf 1811220260) (.leaf 1769347059))) (.branch 43 (.branch 42 (.leaf 1728659577) (.leaf 1689114377)) (.branch 44 (.leaf 1650670018) (.leaf 1613286947))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1576927397) (.branch 47 (.leaf 1541555292) (.leaf 1507136161))) (.branch 50 (.branch 49 (.leaf 1473637050) (.leaf 1441026445)) (.branch 51 (.leaf 1409274199) (.leaf 1378351460)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1348230606) (.leaf 1318885183)) (.branch 55 (.leaf 1290289844) (.leaf 1262420300))) (.branch 58 (.branch 57 (.leaf 1235253258) (.leaf 1208766381)) (.branch 59 (.leaf 1182938236) (.leaf 1157748252))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1133176677) (.branch 62 (.leaf 1109204540) (.leaf 1085813614))) (.branch 65 (.branch 64 (.leaf 1062986378) (.leaf 1040705989)) (.branch 66 (.leaf 1018956245) (.leaf 997721558)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 976986925) (.leaf 956737901)) (.branch 70 (.leaf 936960574) (.leaf 917641542))) (.branch 73 (.branch 72 (.leaf 898767888) (.leaf 880327158)) (.branch 74 (.leaf 862307345) (.leaf 844696862))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 827484532) (.branch 77 (.leaf 810659563) (.leaf 794211535))) (.branch 80 (.branch 79 (.leaf 778130385) (.leaf 762406389)) (.branch 81 (.leaf 747030149) (.leaf 731992581)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 717284898) (.leaf 702898601)) (.branch 85 (.leaf 688825468) (.leaf 675057538))) (.branch 88 (.branch 87 (.leaf 661587108) (.leaf 648406712)) (.branch 89 (.leaf 635509124) (.leaf 622887339)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 610534568) (.branch 92 (.leaf 598444229) (.leaf 586609942))) (.branch 95 (.branch 94 (.leaf 575025514) (.leaf 563684941)) (.branch 96 (.leaf 552582394) (.leaf 541712214)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 531068910) (.leaf 520647146)) (.branch 100 (.leaf 510441740) (.leaf 500447658))) (.branch 103 (.branch 102 (.leaf 490660007) (.leaf 481074029)) (.branch 104 (.leaf 471685102) (.leaf 462488729))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 453480535) (.leaf 444656266)) (.branch 108 (.leaf 436011781) (.leaf 427543051))) (.branch 111 (.branch 110 (.leaf 419246153) (.leaf 411117268)) (.branch 112 (.leaf 403152677) (.leaf 395348757)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 387701981) (.leaf 380208910)) (.branch 116 (.leaf 372866193) (.leaf 365670566))) (.branch 119 (.branch 118 (.leaf 358618845) (.leaf 351707926)) (.branch 120 (.leaf 344934784) (.leaf 338296467)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 830).prefactor = (4600894279187713/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 830).cutoff/(generalMeanRows 830).c)).2 =
    (396199654662389/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 830).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 830).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 830).q*(generalMeanRows 830).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 830).q*(generalMeanRows 830).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 830).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 830

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 830).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 830).criticalRate j.val*(generalMeanRows 830).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 830).c*(generalMeanRows 830).criticalPoint j.val)).2-
      (generalMeanRows 830).J/2-(generalMeanRows 830).error (generalMeanGrid j.val)+
      (generalMeanRows 830).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 830).c)).2-
      (generalMeanRows 830).J/2-(generalMeanRows 830).error 4 := by
  have he : (generalMeanRows 830).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 830) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 830)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0830

/-! Kernel-checked entropy margins for general spectral rectangle 831. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0831
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4937682576) (.branch 2 (.leaf 4767047367) (.leaf 4603989511))) (.branch 5 (.branch 4 (.leaf 4448081687) (.leaf 4298926587)) (.branch 6 (.leaf 4156154299) (.leaf 4019419972)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3888401726) (.leaf 3762798772)) (.branch 10 (.leaf 3642329728) (.leaf 3526731095))) (.branch 13 (.branch 12 (.leaf 3415755878) (.leaf 3309172339)) (.branch 14 (.leaf 3206762864) (.leaf 3108322927))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3013660152) (.branch 17 (.leaf 2922593450) (.leaf 2834952235))) (.branch 20 (.branch 19 (.leaf 2750575696) (.leaf 2669312140)) (.branch 21 (.leaf 2591018378) (.leaf 2515559165)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2442806679) (.leaf 2372640049)) (.branch 25 (.leaf 2304944905) (.leaf 2239612974))) (.branch 28 (.branch 27 (.leaf 2176541695) (.leaf 2115633875)) (.branch 29 (.leaf 2056797354) (.leaf 1999944705)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1944992950) (.branch 32 (.leaf 1891863298) (.leaf 1840480898))) (.branch 35 (.branch 34 (.leaf 1790774612) (.leaf 1742676797)) (.branch 36 (.leaf 1696123110) (.leaf 1651052320)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1607406132) (.leaf 1565129023)) (.branch 40 (.leaf 1524168093) (.leaf 1484472914))) (.branch 43 (.branch 42 (.leaf 1445995405) (.leaf 1408689695)) (.branch 44 (.leaf 1372512014) (.leaf 1337420575))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1303375471) (.branch 47 (.leaf 1270338578) (.leaf 1238273461))) (.branch 50 (.branch 49 (.leaf 1207145285) (.leaf 1176920736)) (.branch 51 (.leaf 1147567944) (.leaf 1119056403)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1091356912) (.leaf 1064441503)) (.branch 55 (.leaf 1038283382) (.leaf 1012856873))) (.branch 58 (.branch 57 (.leaf 988137359) (.leaf 964101235)) (.branch 59 (.leaf 940725855) (.leaf 917989490))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 895871281) (.branch 62 (.leaf 874351199) (.leaf 853410007))) (.branch 65 (.branch 64 (.leaf 833029222) (.leaf 813191077)) (.branch 66 (.leaf 793878495) (.leaf 775075051)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 756764944) (.leaf 738932971)) (.branch 70 (.leaf 721564496) (.leaf 704645429))) (.branch 73 (.branch 72 (.leaf 688162200) (.leaf 672101734)) (.branch 74 (.leaf 656451432) (.leaf 641199149))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 626333177) (.branch 77 (.leaf 611842222) (.leaf 597715388))) (.branch 80 (.branch 79 (.leaf 583942161) (.leaf 570512394)) (.branch 81 (.leaf 557416288) (.leaf 544644381)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 532187531) (.leaf 520036907)) (.branch 85 (.leaf 508183972) (.leaf 496620475))) (.branch 88 (.branch 87 (.leaf 485338435) (.leaf 474330135)) (.branch 89 (.leaf 463588109) (.leaf 453105132)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 442874210) (.branch 92 (.leaf 432888575) (.leaf 423141672))) (.branch 95 (.branch 94 (.leaf 413627150) (.leaf 404338861)) (.branch 96 (.leaf 395270845) (.leaf 386417326)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 377772705) (.leaf 369331555)) (.branch 100 (.leaf 361088612) (.leaf 353038769))) (.branch 103 (.branch 102 (.leaf 345177074) (.leaf 337498720)) (.branch 104 (.leaf 329999043) (.leaf 322673515))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 315517740) (.leaf 308527451)) (.branch 108 (.leaf 301698502) (.leaf 295026865))) (.branch 111 (.branch 110 (.leaf 288508629) (.leaf 282139992)) (.branch 112 (.leaf 275917260) (.leaf 269836842)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 263895246) (.leaf 258089079)) (.branch 116 (.leaf 252415039) (.leaf 246869916))) (.branch 119 (.branch 118 (.leaf 241450587) (.leaf 236154014)) (.branch 120 (.leaf 230977241) (.leaf 225917390)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 831).prefactor = (1183490758460023/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 831).cutoff/(generalMeanRows 831).c)).2 =
    (44662517416583/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 831).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 831).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 831).q*(generalMeanRows 831).c/2-2 = (3421/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable252.value]
    have hcontinuation : (generalMeanRows 831).q*(generalMeanRows 831).cutoff/2-2 = (7766/3731:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable262.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 831).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 831

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 831).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 831).criticalRate j.val*(generalMeanRows 831).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 831).c*(generalMeanRows 831).criticalPoint j.val)).2-
      (generalMeanRows 831).J/2-(generalMeanRows 831).error (generalMeanGrid j.val)+
      (generalMeanRows 831).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 831).c)).2-
      (generalMeanRows 831).J/2-(generalMeanRows 831).error 4 := by
  have he : (generalMeanRows 831).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 831) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 831)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0831

/-! Kernel-checked entropy margins for general spectral rectangle 832. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0832
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5255871993) (.branch 2 (.leaf 5081411406) (.leaf 4914605944))) (.branch 5 (.branch 4 (.leaf 4755023164) (.leaf 4602261086)) (.branch 6 (.leaf 4455945537) (.leaf 4315727771)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4181282348) (.leaf 4052305230)) (.branch 10 (.leaf 3928512061) (.leaf 3809636622))) (.branch 13 (.branch 12 (.leaf 3695429433) (.leaf 3585656483)) (.branch 14 (.leaf 3480098079) (.leaf 3378547796))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3280811521) (.branch 17 (.leaf 3186706578) (.leaf 3096060931))) (.branch 20 (.branch 19 (.leaf 3008712447) (.leaf 2924508224)) (.branch 21 (.leaf 2843303972) (.leaf 2764963440)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2689357894) (.leaf 2616365628)) (.branch 25 (.leaf 2545871514) (.leaf 2477766589))) (.branch 28 (.branch 27 (.leaf 2411947669) (.leaf 2348316990)) (.branch 29 (.leaf 2286781879) (.leaf 2227254441)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2169651278) (.branch 32 (.leaf 2113893214) (.leaf 2059905056))) (.branch 35 (.branch 34 (.leaf 2007615353) (.leaf 1956956181)) (.branch 36 (.leaf 1907862947) (.leaf 1860274189)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1814131410) (.leaf 1769378901)) (.branch 40 (.leaf 1725963598) (.leaf 1683834925))) (.branch 43 (.branch 42 (.leaf 1642944665) (.leaf 1603246831)) (.branch 44 (.leaf 1564697541) (.leaf 1527254914))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1490878953) (.branch 47 (.leaf 1455531455) (.leaf 1421175913))) (.branch 50 (.branch 49 (.leaf 1387777425) (.leaf 1355302618)) (.branch 51 (.leaf 1323719563) (.leaf 1292997703)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1263107788) (.leaf 1234021803)) (.branch 55 (.leaf 1205712908) (.leaf 1178155384))) (.branch 58 (.branch 57 (.leaf 1151324572) (.leaf 1125196823)) (.branch 59 (.leaf 1099749451) (.leaf 1074960684))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1050809619) (.branch 62 (.leaf 1027276186) (.leaf 1004341101))) (.branch 65 (.branch 64 (.leaf 981985834) (.leaf 960192574)) (.branch 66 (.leaf 938944192) (.leaf 918224213)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 898016782) (.leaf 878306642)) (.branch 70 (.leaf 859079099) (.leaf 840320004))) (.branch 73 (.branch 72 (.leaf 822015724) (.leaf 804153120)) (.branch 74 (.leaf 786719528) (.leaf 769702733))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 753090955) (.branch 77 (.leaf 736872826) (.leaf 721037374))) (.branch 80 (.branch 79 (.leaf 705574006) (.leaf 690472494)) (.branch 81 (.leaf 675722954) (.leaf 661315839)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 647241919) (.leaf 633492272)) (.branch 85 (.leaf 620058267) (.leaf 606931557))) (.branch 88 (.branch 87 (.leaf 594104067) (.leaf 581567977)) (.branch 89 (.leaf 569315721) (.leaf 557339970)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 545633626) (.branch 92 (.leaf 534189812) (.leaf 523001863))) (.branch 95 (.branch 94 (.leaf 512063320) (.leaf 501367920)) (.branch 96 (.leaf 490909589) (.leaf 480682435)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 470680744) (.leaf 460898969)) (.branch 100 (.leaf 451331725) (.leaf 441973785))) (.branch 103 (.branch 102 (.leaf 432820074) (.leaf 423865662)) (.branch 104 (.leaf 415105760) (.leaf 406535714))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 398151003) (.leaf 389947230)) (.branch 108 (.leaf 381920122) (.leaf 374065522))) (.branch 111 (.branch 110 (.leaf 366379389) (.leaf 358857792)) (.branch 112 (.leaf 351496904) (.leaf 344293003)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 337242467) (.leaf 330341768)) (.branch 116 (.leaf 323587473) (.leaf 316976239))) (.branch 119 (.branch 118 (.leaf 310504810) (.leaf 304170014)) (.branch 120 (.leaf 297968760) (.leaf 291898040)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 832).prefactor = (2400122182307437/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 832).cutoff/(generalMeanRows 832).c)).2 =
    (37880634455363/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 832).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 832).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 832).q*(generalMeanRows 832).c/2-2 = (1589/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable251.value]
    have hcontinuation : (generalMeanRows 832).q*(generalMeanRows 832).cutoff/2-2 = (7766/3731:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable262.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 832).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 832

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 832).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 832).criticalRate j.val*(generalMeanRows 832).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 832).c*(generalMeanRows 832).criticalPoint j.val)).2-
      (generalMeanRows 832).J/2-(generalMeanRows 832).error (generalMeanGrid j.val)+
      (generalMeanRows 832).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 832).c)).2-
      (generalMeanRows 832).J/2-(generalMeanRows 832).error 4 := by
  have he : (generalMeanRows 832).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 832) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 832)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0832

/-! Kernel-checked entropy margins for general spectral rectangle 833. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0833
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5286811741) (.branch 2 (.leaf 5120050526) (.leaf 4960519613))) (.branch 5 (.branch 4 (.leaf 4807808038) (.leaf 4661533963)) (.branch 6 (.leaf 4521342126) (.leaf 4386901569)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4257903604) (.leaf 4134059986)) (.branch 10 (.leaf 4015101276) (.leaf 3900775351))) (.branch 13 (.branch 12 (.leaf 3790846069) (.leaf 3685092052)) (.branch 14 (.leaf 3583305584) (.leaf 3485291602))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3390866784) (.branch 17 (.leaf 3299858708) (.leaf 3212105088))) (.branch 20 (.branch 19 (.leaf 3127453070) (.leaf 3045758587)) (.branch 21 (.leaf 2966885766) (.leaf 2890706381)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2817099349) (.leaf 2745950266)) (.branch 25 (.leaf 2677150975) (.leaf 2610599170))) (.branch 28 (.branch 27 (.leaf 2546198028) (.leaf 2483855863)) (.branch 29 (.leaf 2423485812) (.leaf 2365005540)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2308336966) (.branch 32 (.leaf 2253406004) (.leaf 2200142330))) (.branch 35 (.branch 34 (.leaf 2148479157) (.leaf 2098353030)) (.branch 36 (.leaf 2049703631) (.leaf 2002473601)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1956608367) (.leaf 1912055989)) (.branch 40 (.leaf 1868767008) (.leaf 1826694313))) (.branch 43 (.branch 42 (.leaf 1785793002) (.leaf 1746020271)) (.branch 44 (.leaf 1707335292) (.leaf 1669699108))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1633074534) (.branch 47 (.leaf 1597426061) (.leaf 1562719766))) (.branch 50 (.branch 49 (.leaf 1528923232) (.leaf 1496005463)) (.branch 51 (.leaf 1463936817) (.leaf 1432688931)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1402234659) (.leaf 1372548005)) (.branch 55 (.leaf 1343604071) (.leaf 1315378998))) (.branch 58 (.branch 57 (.leaf 1287849912) (.leaf 1260994882)) (.branch 59 (.leaf 1234792865) (.leaf 1209223670))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1184267912) (.branch 62 (.leaf 1159906973) (.leaf 1136122969))) (.branch 65 (.branch 64 (.leaf 1112898709) (.leaf 1090217668)) (.branch 66 (.leaf 1068063952) (.leaf 1046422270)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1025277905) (.leaf 1004616687)) (.branch 70 (.leaf 984424970) (.leaf 964689607))) (.branch 73 (.branch 72 (.leaf 945397928) (.leaf 926537717)) (.branch 74 (.leaf 908097191) (.leaf 890064987))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 872430134) (.branch 77 (.leaf 855182045) (.leaf 838310494))) (.branch 80 (.branch 79 (.leaf 821805603) (.leaf 805657827)) (.branch 81 (.leaf 789857941) (.leaf 774397023)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 759266445) (.leaf 744457860)) (.branch 85 (.leaf 729963187) (.leaf 715774606))) (.branch 88 (.branch 87 (.leaf 701884542) (.leaf 688285660)) (.branch 89 (.leaf 674970851) (.leaf 661933225)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 649166104) (.branch 92 (.leaf 636663009) (.leaf 624417658))) (.branch 95 (.branch 94 (.leaf 612423956) (.leaf 600675987)) (.branch 96 (.leaf 589168006) (.leaf 577894437)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 566849865) (.leaf 556029026)) (.branch 100 (.leaf 545426808) (.leaf 535038241))) (.branch 103 (.branch 102 (.leaf 524858492) (.leaf 514882865)) (.branch 104 (.leaf 505106789) (.leaf 495525819))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 486135628) (.leaf 476932007)) (.branch 108 (.leaf 467910857) (.leaf 459068188))) (.branch 111 (.branch 110 (.leaf 450400113) (.leaf 441902848)) (.branch 112 (.leaf 433572704) (.leaf 425406088)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 417399498) (.leaf 409549520)) (.branch 116 (.leaf 401852826) (.leaf 394306170))) (.branch 119 (.branch 118 (.leaf 386906387) (.leaf 379650390)) (.branch 120 (.leaf 372535166) (.leaf 365557776)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 833).prefactor = (4591678009207839/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 833).cutoff/(generalMeanRows 833).c)).2 =
    (408948561911567/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 833).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 833).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 833).q*(generalMeanRows 833).c/2-2 = (73/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable024.value]
    have hcontinuation : (generalMeanRows 833).q*(generalMeanRows 833).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable123.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 833).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 833

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 833).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 833).criticalRate j.val*(generalMeanRows 833).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 833).c*(generalMeanRows 833).criticalPoint j.val)).2-
      (generalMeanRows 833).J/2-(generalMeanRows 833).error (generalMeanGrid j.val)+
      (generalMeanRows 833).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 833).c)).2-
      (generalMeanRows 833).J/2-(generalMeanRows 833).error 4 := by
  have he : (generalMeanRows 833).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 833) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 833)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0833

/-! Kernel-checked entropy margins for general spectral rectangle 834. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0834
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5015491118) (.branch 2 (.leaf 4842290024) (.leaf 4676753743))) (.branch 5 (.branch 4 (.leaf 4518451811) (.leaf 4366983927)) (.branch 6 (.leaf 4221977323) (.leaf 4083084415)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3949980701) (.leaf 3822362878)) (.branch 10 (.leaf 3699947148) (.leaf 3582467686))) (.branch 13 (.branch 12 (.leaf 3469675259) (.leaf 3361335970)) (.branch 14 (.leaf 3257230125) (.leaf 3157151189))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3060904848) (.branch 17 (.leaf 2968308141) (.leaf 2879188671))) (.branch 20 (.branch 19 (.leaf 2793383880) (.leaf 2710740383)) (.branch 21 (.leaf 2631113358) (.leaf 2554365978)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2480368896) (.leaf 2408999759)) (.branch 25 (.leaf 2340142768) (.leaf 2273688268))) (.branch 28 (.branch 27 (.leaf 2209532362) (.leaf 2147576560)) (.branch 29 (.leaf 2087727453) (.leaf 2029896403)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1973999263) (.branch 32 (.leaf 1919956109) (.leaf 1867690997))) (.branch 35 (.branch 34 (.leaf 1817131729) (.leaf 1768209642)) (.branch 36 (.leaf 1720859403) (.leaf 1675018825)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1630628690) (.leaf 1587632582)) (.branch 40 (.leaf 1545976737) (.leaf 1505609897))) (.branch 43 (.branch 42 (.leaf 1466483172) (.leaf 1428549916)) (.branch 44 (.leaf 1391765605) (.leaf 1356087728))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1321475678) (.branch 47 (.leaf 1287890651) (.leaf 1255295561))) (.branch 50 (.branch 49 (.leaf 1223654941) (.leaf 1192934869)) (.branch 51 (.leaf 1163102884) (.leaf 1134127915)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1105980212) (.leaf 1078631278)) (.branch 55 (.leaf 1052053810) (.leaf 1026221637))) (.branch 58 (.branch 57 (.leaf 1001109669) (.leaf 976693841)) (.branch 59 (.leaf 952951066) (.leaf 929859186))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 907396933) (.branch 62 (.leaf 885543880) (.leaf 864280405))) (.branch 65 (.branch 64 (.leaf 843587657) (.leaf 823447514)) (.branch 66 (.leaf 803842552) (.leaf 784756017)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 766171787) (.leaf 748074350)) (.branch 70 (.leaf 730448775) (.leaf 713280684))) (.branch 73 (.branch 72 (.leaf 696556229) (.leaf 680262069)) (.branch 74 (.leaf 664385350) (.leaf 648913677))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 633835103) (.branch 77 (.leaf 619138104) (.leaf 604811561))) (.branch 80 (.branch 79 (.leaf 590844747) (.leaf 577227306)) (.branch 81 (.leaf 563949242) (.leaf 551000899)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 538372951) (.leaf 526056388)) (.branch 85 (.leaf 514042500) (.leaf 502322870))) (.branch 88 (.branch 87 (.leaf 490889357) (.leaf 479734089)) (.branch 89 (.leaf 468849451) (.leaf 458228075)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 447862828) (.branch 92 (.leaf 437746807) (.leaf 427873329))) (.branch 95 (.branch 94 (.leaf 418235920) (.leaf 408828309)) (.branch 96 (.leaf 399644422) (.leaf 390678371)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 381924450) (.leaf 373377127)) (.branch 100 (.leaf 365031037) (.leaf 356880977))) (.branch 103 (.branch 102 (.leaf 348921902) (.leaf 341148915)) (.branch 104 (.leaf 333557264) (.leaf 326142338))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 318899659) (.leaf 311824882)) (.branch 108 (.leaf 304913786) (.leaf 298162269))) (.branch 111 (.branch 110 (.leaf 291566351) (.leaf 285122161)) (.branch 112 (.leaf 278825940) (.leaf 272674032)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 266662886) (.leaf 260789048)) (.branch 116 (.leaf 255049161) (.leaf 249439957))) (.branch 119 (.branch 118 (.leaf 243958262) (.leaf 238600985)) (.branch 120 (.leaf 233365120) (.leaf 228247742)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 834).prefactor = (74660140589759/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 834).cutoff/(generalMeanRows 834).c)).2 =
    (8795516839201/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 834).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 834).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 834).q*(generalMeanRows 834).c/2-2 = (3421/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable252.value]
    have hcontinuation : (generalMeanRows 834).q*(generalMeanRows 834).cutoff/2-2 = (5150/2501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable264.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 834).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 834

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 834).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 834).criticalRate j.val*(generalMeanRows 834).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 834).c*(generalMeanRows 834).criticalPoint j.val)).2-
      (generalMeanRows 834).J/2-(generalMeanRows 834).error (generalMeanGrid j.val)+
      (generalMeanRows 834).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 834).c)).2-
      (generalMeanRows 834).J/2-(generalMeanRows 834).error 4 := by
  have he : (generalMeanRows 834).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 834) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 834)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0834

/-! Kernel-checked entropy margins for general spectral rectangle 835. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0835
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5107823365) (.branch 2 (.leaf 4939681722) (.leaf 4778884955))) (.branch 5 (.branch 4 (.leaf 4625018576) (.leaf 4477697305)) (.branch 6 (.leaf 4336562519) (.leaf 4201279979)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4071537786) (.leaf 3947044558)) (.branch 10 (.leaf 3827527782) (.leaf 3712732332))) (.branch 13 (.branch 12 (.leaf 3602419126) (.leaf 3496363908)) (.branch 14 (.leaf 3394356146) (.leaf 3296198023))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3201703524) (.branch 17 (.leaf 3110697592) (.leaf 3023015367))) (.branch 20 (.branch 19 (.leaf 2938501478) (.leaf 2857009397)) (.branch 21 (.leaf 2778400851) (.leaf 2702545267)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2629319274) (.leaf 2558606232)) (.branch 25 (.leaf 2490295807) (.leaf 2424283566))) (.branch 28 (.branch 27 (.leaf 2360470614) (.leaf 2298763248)) (.branch 29 (.leaf 2239072637) (.leaf 2181314532)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2125408987) (.branch 32 (.leaf 2071280102) (.leaf 2018855789))) (.branch 35 (.branch 34 (.leaf 1968067543) (.leaf 1918850242)) (.branch 36 (.leaf 1871141946) (.leaf 1824883720)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1780019461) (.leaf 1736495745)) (.branch 40 (.leaf 1694261670) (.leaf 1653268724))) (.branch 43 (.branch 42 (.leaf 1613470651) (.leaf 1574823330)) (.branch 44 (.leaf 1537284656) (.leaf 1500814437))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1465374292) (.branch 47 (.leaf 1430927549) (.leaf 1397439166))) (.branch 50 (.branch 49 (.leaf 1364875635) (.leaf 1333204911)) (.branch 51 (.leaf 1302396334) (.leaf 1272420559)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1243249487) (.leaf 1214856205)) (.branch 55 (.leaf 1187214926) (.leaf 1160300935))) (.branch 58 (.branch 57 (.leaf 1134090532) (.leaf 1108560984)) (.branch 59 (.leaf 1083690481) (.leaf 1059458088))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1035843703) (.branch 62 (.leaf 1012828019) (.leaf 990392485))) (.branch 65 (.branch 64 (.leaf 968519272) (.leaf 947191238)) (.branch 66 (.leaf 926391896) (.leaf 906105383)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 886316434) (.leaf 867010353)) (.branch 70 (.leaf 848172987) (.leaf 829790703))) (.branch 73 (.branch 72 (.leaf 811850363) (.leaf 794339303)) (.branch 74 (.leaf 777245313) (.leaf 760556615))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 744261848) (.branch 77 (.leaf 728350045) (.leaf 712810620))) (.branch 80 (.branch 79 (.leaf 697633350) (.leaf 682808361)) (.branch 81 (.leaf 668326111) (.leaf 654177379)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 640353250) (.leaf 626845104)) (.branch 85 (.leaf 613644601) (.leaf 600743673))) (.branch 88 (.branch 87 (.leaf 588134511) (.leaf 575809556)) (.branch 89 (.leaf 563761488) (.leaf 551983217)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 540467874) (.branch 92 (.leaf 529208803) (.leaf 518199553))) (.branch 95 (.branch 94 (.leaf 507433867) (.leaf 496905681)) (.branch 96 (.leaf 486609109) (.leaf 476538443)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 466688144) (.leaf 457052834)) (.branch 100 (.leaf 447627292) (.leaf 438406450))) (.branch 103 (.branch 102 (.leaf 429385382) (.leaf 420559305)) (.branch 104 (.leaf 411923572) (.leaf 403473665))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 395205192) (.leaf 387113885)) (.branch 108 (.leaf 379195593) (.leaf 371446276))) (.branch 111 (.branch 110 (.leaf 363862007) (.leaf 356438964)) (.branch 112 (.leaf 349173427) (.leaf 342061777)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 335100489) (.leaf 328286133)) (.branch 116 (.leaf 321615367) (.leaf 315084936))) (.branch 119 (.branch 118 (.leaf 308691672) (.leaf 302432484)) (.branch 120 (.leaf 296304366) (.leaf 290304383)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 835).prefactor = (1158215760215327/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 835).cutoff/(generalMeanRows 835).c)).2 =
    (76351794101519/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 835).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 835).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 835).q*(generalMeanRows 835).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 835).q*(generalMeanRows 835).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 835).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 835

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 835).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 835).criticalRate j.val*(generalMeanRows 835).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 835).c*(generalMeanRows 835).criticalPoint j.val)).2-
      (generalMeanRows 835).J/2-(generalMeanRows 835).error (generalMeanGrid j.val)+
      (generalMeanRows 835).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 835).c)).2-
      (generalMeanRows 835).J/2-(generalMeanRows 835).error 4 := by
  have he : (generalMeanRows 835).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 835) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 835)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0835

/-! Kernel-checked entropy margins for general spectral rectangle 836. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0836
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5227673875) (.branch 2 (.leaf 5057974684) (.leaf 4895660765))) (.branch 5 (.branch 4 (.leaf 4740314994) (.leaf 4591549675)) (.branch 6 (.leaf 4449003963) (.leaf 4312341574)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4181248729) (.leaf 4055432313)) (.branch 10 (.leaf 3934618218) (.leaf 3818549845))) (.branch 13 (.branch 12 (.leaf 3706986755) (.leaf 3599703441)) (.branch 14 (.leaf 3496488214) (.leaf 3397142192))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3301478371) (.branch 17 (.leaf 3209320787) (.leaf 3120503737))) (.branch 20 (.branch 19 (.leaf 3034871073) (.leaf 2952275552)) (.branch 21 (.leaf 2872578235) (.leaf 2795647938)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2721360722) (.leaf 2649599425)) (.branch 25 (.leaf 2580253228) (.leaf 2513217254))) (.branch 28 (.branch 27 (.leaf 2448392192) (.leaf 2385683959)) (.branch 29 (.leaf 2325003373) (.leaf 2266265857)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2209391165) (.branch 32 (.leaf 2154303120) (.leaf 2100929377))) (.branch 35 (.branch 34 (.leaf 2049201195) (.leaf 1999053232)) (.branch 36 (.leaf 1950423347) (.leaf 1903252417)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1857484169) (.leaf 1813065016)) (.branch 40 (.leaf 1769943912) (.leaf 1728072208))) (.branch 43 (.branch 42 (.leaf 1687403523) (.leaf 1647893617)) (.branch 44 (.leaf 1609500280) (.leaf 1572183219))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1535903960) (.branch 47 (.leaf 1500625746) (.leaf 1466313454))) (.branch 50 (.branch 49 (.leaf 1432933503) (.leaf 1400453779)) (.branch 51 (.leaf 1368843557) (.leaf 1338073431)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1308115246) (.leaf 1278942036)) (.branch 55 (.leaf 1250527965) (.leaf 1222848269))) (.branch 58 (.branch 57 (.leaf 1195879203) (.leaf 1169597995)) (.branch 59 (.leaf 1143982791) (.leaf 1119012618))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1094667338) (.branch 62 (.leaf 1070927608) (.leaf 1047774843))) (.branch 65 (.branch 64 (.leaf 1025191180) (.leaf 1003159443)) (.branch 66 (.leaf 981663114) (.leaf 960686300)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 940213704) (.leaf 920230600)) (.branch 70 (.leaf 900722805) (.leaf 881676655))) (.branch 73 (.branch 72 (.leaf 863078984) (.leaf 844917098)) (.branch 74 (.leaf 827178757) (.leaf 809852154))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 792925897) (.branch 77 (.leaf 776388989) (.leaf 760230815))) (.branch 80 (.branch 79 (.leaf 744441120) (.leaf 729010001)) (.branch 81 (.leaf 713927885) (.leaf 699185518)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 684773956) (.leaf 670684544)) (.branch 85 (.leaf 656908912) (.leaf 643438958))) (.branch 88 (.branch 87 (.leaf 630266841) (.leaf 617384968)) (.branch 89 (.leaf 604785985) (.leaf 592462767)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 580408412) (.branch 92 (.leaf 568616227) (.leaf 557079726))) (.branch 95 (.branch 94 (.leaf 545792618) (.leaf 534748800)) (.branch 96 (.leaf 523942352) (.leaf 513367528)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 503018750) (.leaf 492890604)) (.branch 100 (.leaf 482977831) (.leaf 473275323))) (.branch 103 (.branch 102 (.leaf 463778117) (.leaf 454481391)) (.branch 104 (.leaf 445380457) (.leaf 436470759))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 427747865) (.leaf 419207466)) (.branch 108 (.leaf 410845371) (.leaf 402657499))) (.branch 111 (.branch 110 (.leaf 394639883) (.leaf 386788660)) (.branch 112 (.leaf 379100069) (.leaf 371570448)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 364196232) (.leaf 356973948)) (.branch 116 (.leaf 349900213) (.leaf 342971731))) (.branch 119 (.branch 118 (.leaf 336185290) (.leaf 329537759)) (.branch 120 (.leaf 323026087) (.leaf 316647299)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 836).prefactor = (58313174170479/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 836).cutoff/(generalMeanRows 836).c)).2 =
    (388953246141621/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 836).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 836).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 836).q*(generalMeanRows 836).c/2-2 = (77/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable254.value]
    have hcontinuation : (generalMeanRows 836).q*(generalMeanRows 836).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 836).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 836

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 836).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 836).criticalRate j.val*(generalMeanRows 836).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 836).c*(generalMeanRows 836).criticalPoint j.val)).2-
      (generalMeanRows 836).J/2-(generalMeanRows 836).error (generalMeanGrid j.val)+
      (generalMeanRows 836).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 836).c)).2-
      (generalMeanRows 836).J/2-(generalMeanRows 836).error 4 := by
  have he : (generalMeanRows 836).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 836) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 836)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0836

/-! Kernel-checked entropy margins for general spectral rectangle 837. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0837
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5215038188) (.branch 2 (.leaf 5043367199) (.leaf 4879195258))) (.branch 5 (.branch 4 (.leaf 4722099174) (.leaf 4571685583)) (.branch 6 (.leaf 4427588334) (.leaf 4289466171)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4157000648) (.leaf 4029894268)) (.branch 10 (.leaf 3907868797) (.leaf 3790663755))) (.branch 13 (.branch 12 (.leaf 3678035039) (.leaf 3569753689)) (.branch 14 (.leaf 3465604751) (.leaf 3365386259))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3268908290) (.branch 17 (.leaf 3175992116) (.leaf 3086469413))) (.branch 20 (.branch 19 (.leaf 3000181550) (.leaf 2916978925)) (.branch 21 (.leaf 2836720361) (.leaf 2759272545)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2684509514) (.leaf 2612312184)) (.branch 25 (.leaf 2542567901) (.leaf 2475170043))) (.branch 28 (.branch 27 (.leaf 2410017637) (.leaf 2347015013)) (.branch 29 (.leaf 2286071478) (.leaf 2227101012)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2170021992) (.branch 32 (.leaf 2114756925) (.leaf 2061232208))) (.branch 35 (.branch 34 (.leaf 2009377902) (.leaf 1959127514)) (.branch 36 (.leaf 1910417806) (.leaf 1863188605)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1817382631) (.leaf 1772945338)) (.branch 40 (.leaf 1729824756) (.leaf 1687971356))) (.branch 43 (.branch 42 (.leaf 1647337909) (.leaf 1607879368)) (.branch 44 (.leaf 1569552745) (.leaf 1532317006))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1496132960) (.branch 47 (.leaf 1460963170) (.leaf 1426771854))) (.branch 50 (.branch 49 (.leaf 1393524805) (.leaf 1361189302)) (.branch 51 (.leaf 1329734044) (.leaf 1299129068)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1269345685) (.leaf 1240356419)) (.branch 55 (.leaf 1212134942) (.leaf 1184656018))) (.branch 58 (.branch 57 (.leaf 1157895449) (.leaf 1131830029)) (.branch 59 (.leaf 1106437486) (.leaf 1081696447))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1057586389) (.branch 62 (.leaf 1034087598) (.leaf 1011181136))) (.branch 65 (.branch 64 (.leaf 988848797) (.leaf 967073081)) (.branch 66 (.leaf 945837154) (.leaf 925124821)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 904920496) (.leaf 885209174)) (.branch 70 (.leaf 865976406) (.leaf 847208271))) (.branch 73 (.branch 72 (.leaf 828891358) (.leaf 811012735)) (.branch 74 (.leaf 793559937) (.leaf 776520939))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 759884139) (.branch 77 (.leaf 743638342) (.leaf 727772740))) (.branch 80 (.branch 79 (.leaf 712276894) (.leaf 697140724)) (.branch 81 (.leaf 682354487) (.leaf 667908768)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 653794467) (.leaf 640002780)) (.branch 85 (.leaf 626525195) (.leaf 613353472))) (.branch 88 (.branch 87 (.leaf 600479640) (.leaf 587895980)) (.branch 89 (.leaf 575595020) (.leaf 563569519)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 551812465) (.branch 92 (.leaf 540317063) (.leaf 529076725))) (.branch 95 (.branch 94 (.leaf 518085064) (.leaf 507335887)) (.branch 96 (.leaf 496823187) (.leaf 486541136)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 476484075) (.leaf 466646517)) (.branch 100 (.leaf 457023130) (.leaf 447608739))) (.branch 103 (.branch 102 (.leaf 438398316) (.leaf 429386977)) (.branch 104 (.leaf 420569977) (.leaf 411942704))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 403500674) (.leaf 395239528)) (.branch 108 (.leaf 387155028) (.leaf 379243050))) (.branch 111 (.branch 110 (.leaf 371499585) (.leaf 363920730)) (.branch 112 (.leaf 356502687) (.leaf 349241762)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 342134354) (.leaf 335176963)) (.branch 116 (.leaf 328366175) (.leaf 321698668))) (.branch 119 (.branch 118 (.leaf 315171207) (.leaf 308780638)) (.branch 120 (.leaf 302523888) (.leaf 296397963)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 837).prefactor = (1182527074258081/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 837).cutoff/(generalMeanRows 837).c)).2 =
    (76351794101519/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 837).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 837).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 837).q*(generalMeanRows 837).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 837).q*(generalMeanRows 837).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 837).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 837

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 837).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 837).criticalRate j.val*(generalMeanRows 837).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 837).c*(generalMeanRows 837).criticalPoint j.val)).2-
      (generalMeanRows 837).J/2-(generalMeanRows 837).error (generalMeanGrid j.val)+
      (generalMeanRows 837).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 837).c)).2-
      (generalMeanRows 837).J/2-(generalMeanRows 837).error 4 := by
  have he : (generalMeanRows 837).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 837) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 837)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0837

/-! Kernel-checked entropy margins for general spectral rectangle 838. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0838
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5646079593) (.branch 2 (.leaf 5463855885) (.leaf 5289563034))) (.branch 5 (.branch 4 (.leaf 5122753355) (.leaf 4963010701)) (.branch 6 (.leaf 4809947702) (.leaf 4663203313)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4522440611) (.leaf 4387344824)) (.branch 10 (.leaf 4257621552) (.leaf 4132995171))) (.branch 13 (.branch 12 (.leaf 4013207382) (.leaf 3898015897)) (.branch 14 (.leaf 3787193252) (.leaf 3680525717))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3577812306) (.branch 17 (.leaf 3478863880) (.leaf 3383502309))) (.branch 20 (.branch 19 (.leaf 3291559723) (.leaf 3202877806)) (.branch 21 (.leaf 3117307162) (.leaf 3034706723)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2954943202) (.leaf 2877890594)) (.branch 25 (.leaf 2803429707) (.leaf 2731447735))) (.branch 28 (.branch 27 (.leaf 2661837860) (.leaf 2594498877)) (.branch 29 (.leaf 2529334856) (.leaf 2466254819)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2405172446) (.branch 32 (.leaf 2346005795) (.leaf 2288677045))) (.branch 35 (.branch 34 (.leaf 2233112259) (.leaf 2179241154)) (.branch 36 (.leaf 2126996895) (.leaf 2076315896)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2027137641) (.leaf 1979404507)) (.branch 40 (.leaf 1933061606) (.leaf 1888056635))) (.branch 43 (.branch 42 (.leaf 1844339733) (.leaf 1801863347)) (.branch 44 (.leaf 1760582112) (.leaf 1720452728))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1681433855) (.branch 47 (.leaf 1643486007) (.leaf 1606571456))) (.branch 50 (.branch 49 (.leaf 1570654139) (.leaf 1535699573)) (.branch 51 (.leaf 1501674773) (.leaf 1468548176)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1436289569) (.leaf 1404870022)) (.branch 55 (.leaf 1374261818) (.leaf 1344438403))) (.branch 58 (.branch 57 (.leaf 1315374316) (.leaf 1287045148)) (.branch 59 (.leaf 1259427480) (.leaf 1232498842))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1206237662) (.branch 62 (.leaf 1180623227) (.leaf 1155635642))) (.branch 65 (.branch 64 (.leaf 1131255788) (.leaf 1107465289)) (.branch 66 (.leaf 1084246473) (.leaf 1061582346)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1039456555) (.leaf 1017853359)) (.branch 70 (.leaf 996757605) (.leaf 976154698))) (.branch 73 (.branch 72 (.leaf 956030578) (.leaf 936371692)) (.branch 74 (.leaf 917164978) (.leaf 898397839))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 880058122) (.branch 77 (.leaf 862134102) (.leaf 844614462))) (.branch 80 (.branch 79 (.leaf 827488273) (.leaf 810744983)) (.branch 81 (.leaf 794374395) (.leaf 778366656)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 762712242) (.leaf 747401943)) (.branch 85 (.leaf 732426853) (.leaf 717778351))) (.branch 88 (.branch 87 (.leaf 703448100) (.leaf 689428025)) (.branch 89 (.leaf 675710308) (.leaf 662287379)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 649151902) (.branch 92 (.leaf 636296768) (.leaf 623715087))) (.branch 95 (.branch 94 (.leaf 611400179) (.leaf 599345564)) (.branch 96 (.leaf 587544959) (.leaf 575992263)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564681560) (.leaf 553607104)) (.branch 100 (.leaf 542763316) (.leaf 532144778))) (.branch 103 (.branch 102 (.leaf 521746227) (.leaf 511562548)) (.branch 104 (.leaf 501588772) (.leaf 491820068))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 482251737) (.leaf 472879212)) (.branch 108 (.leaf 463698049) (.leaf 454703925))) (.branch 111 (.branch 110 (.leaf 445892634) (.leaf 437260082)) (.branch 112 (.leaf 428802283) (.leaf 420515357)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 412395526) (.leaf 404439108)) (.branch 116 (.leaf 396642519) (.leaf 389002266))) (.branch 119 (.branch 118 (.leaf 381514944) (.leaf 374177235)) (.branch 120 (.leaf 366985906) (.leaf 359937802)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 838).prefactor = (4951542943138281/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 838).cutoff/(generalMeanRows 838).c)).2 =
    (389632333991831/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 838).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 838).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 838).q*(generalMeanRows 838).c/2-2 = (747/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable220.value]
    have hcontinuation : (generalMeanRows 838).q*(generalMeanRows 838).cutoff/2-2 = (7814/3801:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable261.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 838).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 838

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 838).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 838).criticalRate j.val*(generalMeanRows 838).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 838).c*(generalMeanRows 838).criticalPoint j.val)).2-
      (generalMeanRows 838).J/2-(generalMeanRows 838).error (generalMeanGrid j.val)+
      (generalMeanRows 838).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 838).c)).2-
      (generalMeanRows 838).J/2-(generalMeanRows 838).error 4 := by
  have he : (generalMeanRows 838).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 838) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 838)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0838

/-! Kernel-checked entropy margins for general spectral rectangle 839. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0839
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4917501389) (.branch 2 (.leaf 4745234506) (.leaf 4580675834))) (.branch 5 (.branch 4 (.leaf 4423388994) (.leaf 4272968309)) (.branch 6 (.leaf 4129036122) (.leaf 3991240409)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3859252637) (.leaf 3732765852)) (.branch 10 (.leaf 3611492945) (.leaf 3495165099))) (.branch 13 (.branch 12 (.leaf 3383530374) (.leaf 3276352436)) (.branch 14 (.leaf 3173409391) (.leaf 3074492729))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2979406363) (.branch 17 (.leaf 2887965745) (.leaf 2799997061))) (.branch 20 (.branch 19 (.leaf 2715336490) (.leaf 2633829529)) (.branch 21 (.leaf 2555330365) (.leaf 2479701298)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2406812217) (.leaf 2336540105)) (.branch 25 (.leaf 2268768587) (.leaf 2203387513))) (.branch 28 (.branch 27 (.leaf 2140292565) (.leaf 2079384901)) (.branch 29 (.leaf 2020570821) (.leaf 1963761449)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1908872453) (.branch 32 (.leaf 1855823769) (.leaf 1804539350))) (.branch 35 (.branch 34 (.leaf 1754946937) (.leaf 1706977836)) (.branch 36 (.leaf 1660566712) (.leaf 1615651405)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1572172744) (.leaf 1530074386)) (.branch 40 (.leaf 1489302654) (.leaf 1449806394))) (.branch 43 (.branch 42 (.leaf 1411536837) (.leaf 1374447469)) (.branch 44 (.leaf 1338493908) (.leaf 1303633795))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1269826683) (.branch 47 (.leaf 1237033936) (.leaf 1205218638))) (.branch 50 (.branch 49 (.leaf 1174345502) (.leaf 1144380784)) (.branch 51 (.leaf 1115292207) (.leaf 1087048888)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1059621260) (.leaf 1032981017)) (.branch 55 (.leaf 1007101042) (.leaf 981955353))) (.branch 58 (.branch 57 (.leaf 957519045) (.leaf 933768241)) (.branch 59 (.leaf 910680037) (.leaf 888232460))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 866404419) (.branch 62 (.leaf 845175669) (.leaf 824526764))) (.branch 65 (.branch 64 (.leaf 804439026) (.leaf 784894504)) (.branch 66 (.leaf 765875943) (.leaf 747366753)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 729350977) (.leaf 711813262)) (.branch 70 (.leaf 694738831) (.leaf 678113461))) (.branch 73 (.branch 72 (.leaf 661923455) (.leaf 646155619)) (.branch 74 (.leaf 630797242) (.leaf 615836071))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 601260297) (.branch 77 (.leaf 587058529) (.leaf 573219782))) (.branch 80 (.branch 79 (.leaf 559733458) (.leaf 546589327)) (.branch 81 (.leaf 533777515) (.leaf 521288487)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 509113035) (.leaf 497242263)) (.branch 85 (.leaf 485667574) (.leaf 474380660))) (.branch 88 (.branch 87 (.leaf 463373489) (.leaf 452638292)) (.branch 89 (.leaf 442167556) (.leaf 431954014)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 421990630) (.branch 92 (.leaf 412270598) (.leaf 402787325))) (.branch 95 (.branch 94 (.leaf 393534432) (.leaf 384505735)) (.branch 96 (.leaf 375695247) (.leaf 367097166)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 358705870) (.leaf 350515907)) (.branch 100 (.leaf 342521993) (.leaf 334719004))) (.branch 103 (.branch 102 (.leaf 327101969) (.leaf 319666068)) (.branch 104 (.leaf 312406622) (.leaf 305319092))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 298399070) (.leaf 291642281)) (.branch 108 (.leaf 285044569) (.leaf 278601902))) (.branch 111 (.branch 110 (.leaf 272310362) (.leaf 266166144)) (.branch 112 (.leaf 260165550) (.leaf 254304988)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 248580965) (.leaf 242990087)) (.branch 116 (.leaf 237529055) (.leaf 232194660))) (.branch 119 (.branch 118 (.leaf 226983781) (.leaf 221893385)) (.branch 120 (.leaf 216920520) (.leaf 212062314)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 839).prefactor = (1205359285891651/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 839).cutoff/(generalMeanRows 839).c)).2 =
    (355742627920543/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 839).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 839).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 839).q*(generalMeanRows 839).c/2-2 = (1751/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable267.value]
    have hcontinuation : (generalMeanRows 839).q*(generalMeanRows 839).cutoff/2-2 = (15614/7421:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable266.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 839).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 839

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 839).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 839).criticalRate j.val*(generalMeanRows 839).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 839).c*(generalMeanRows 839).criticalPoint j.val)).2-
      (generalMeanRows 839).J/2-(generalMeanRows 839).error (generalMeanGrid j.val)+
      (generalMeanRows 839).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 839).c)).2-
      (generalMeanRows 839).J/2-(generalMeanRows 839).error 4 := by
  have he : (generalMeanRows 839).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 839) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 839)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0839

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock11 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 11 i) := by
  fin_cases i
  · exact EntropyRow0770.numerical
  · exact EntropyRow0771.numerical
  · exact EntropyRow0772.numerical
  · exact EntropyRow0773.numerical
  · exact EntropyRow0774.numerical
  · exact EntropyRow0775.numerical
  · exact EntropyRow0776.numerical
  · exact EntropyRow0777.numerical
  · exact EntropyRow0778.numerical
  · exact EntropyRow0779.numerical
  · exact EntropyRow0780.numerical
  · exact EntropyRow0781.numerical
  · exact EntropyRow0782.numerical
  · exact EntropyRow0783.numerical
  · exact EntropyRow0784.numerical
  · exact EntropyRow0785.numerical
  · exact EntropyRow0786.numerical
  · exact EntropyRow0787.numerical
  · exact EntropyRow0788.numerical
  · exact EntropyRow0789.numerical
  · exact EntropyRow0790.numerical
  · exact EntropyRow0791.numerical
  · exact EntropyRow0792.numerical
  · exact EntropyRow0793.numerical
  · exact EntropyRow0794.numerical
  · exact EntropyRow0795.numerical
  · exact EntropyRow0796.numerical
  · exact EntropyRow0797.numerical
  · exact EntropyRow0798.numerical
  · exact EntropyRow0799.numerical
  · exact EntropyRow0800.numerical
  · exact EntropyRow0801.numerical
  · exact EntropyRow0802.numerical
  · exact EntropyRow0803.numerical
  · exact EntropyRow0804.numerical
  · exact EntropyRow0805.numerical
  · exact EntropyRow0806.numerical
  · exact EntropyRow0807.numerical
  · exact EntropyRow0808.numerical
  · exact EntropyRow0809.numerical
  · exact EntropyRow0810.numerical
  · exact EntropyRow0811.numerical
  · exact EntropyRow0812.numerical
  · exact EntropyRow0813.numerical
  · exact EntropyRow0814.numerical
  · exact EntropyRow0815.numerical
  · exact EntropyRow0816.numerical
  · exact EntropyRow0817.numerical
  · exact EntropyRow0818.numerical
  · exact EntropyRow0819.numerical
  · exact EntropyRow0820.numerical
  · exact EntropyRow0821.numerical
  · exact EntropyRow0822.numerical
  · exact EntropyRow0823.numerical
  · exact EntropyRow0824.numerical
  · exact EntropyRow0825.numerical
  · exact EntropyRow0826.numerical
  · exact EntropyRow0827.numerical
  · exact EntropyRow0828.numerical
  · exact EntropyRow0829.numerical
  · exact EntropyRow0830.numerical
  · exact EntropyRow0831.numerical
  · exact EntropyRow0832.numerical
  · exact EntropyRow0833.numerical
  · exact EntropyRow0834.numerical
  · exact EntropyRow0835.numerical
  · exact EntropyRow0836.numerical
  · exact EntropyRow0837.numerical
  · exact EntropyRow0838.numerical
  · exact EntropyRow0839.numerical
end SingularValueBounds.KL.Certificates
