import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block09
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block12
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block13
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block14
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block16
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block17
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block18
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 840. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0840
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5463646687) (.branch 2 (.leaf 5279861183) (.leaf 5104134601))) (.branch 5 (.branch 4 (.leaf 4936015060) (.leaf 4775082341)) (.branch 6 (.leaf 4620945124) (.leaf 4473238522)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4331621878) (.leaf 4195776780)) (.branch 10 (.leaf 4065405287) (.leaf 3940228320))) (.branch 13 (.branch 12 (.leaf 3819984213) (.leaf 3704427397)) (.branch 14 (.leaf 3593327203) (.leaf 3486466778))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3383642093) (.branch 17 (.leaf 3284661033) (.leaf 3189342572))) (.branch 20 (.branch 19 (.leaf 3097516013) (.leaf 3009020285)) (.branch 21 (.leaf 2923703307) (.leaf 2841421389)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2762038695) (.leaf 2685426733)) (.branch 25 (.leaf 2611463890) (.leaf 2540035003))) (.branch 28 (.branch 27 (.leaf 2471030956) (.leaf 2404348312)) (.branch 29 (.leaf 2339888968) (.leaf 2277559831)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2217272524) (.branch 32 (.leaf 2158943107) (.leaf 2102491818))) (.branch 35 (.branch 34 (.leaf 2047842830) (.leaf 1994924029)) (.branch 36 (.leaf 1943666799) (.leaf 1894005826)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1845878918) (.leaf 1799226825)) (.branch 40 (.leaf 1753993082) (.leaf 1710123855))) (.branch 43 (.branch 42 (.leaf 1667567800) (.leaf 1626275929)) (.branch 44 (.leaf 1586201484) (.leaf 1547299817))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1509528285) (.branch 47 (.leaf 1472846138) (.leaf 1437214425))) (.branch 50 (.branch 49 (.leaf 1402595904) (.leaf 1368954947)) (.branch 51 (.leaf 1336257466) (.leaf 1304470830)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1273563797) (.leaf 1243506437)) (.branch 55 (.leaf 1214270078) (.leaf 1185827233))) (.branch 58 (.branch 57 (.leaf 1158151550) (.leaf 1131217755)) (.branch 59 (.leaf 1105001599) (.leaf 1079479808))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1054630039) (.branch 62 (.leaf 1030430838) (.leaf 1006861590))) (.branch 65 (.branch 64 (.leaf 983902489) (.leaf 961534497)) (.branch 66 (.leaf 939739305) (.leaf 918499306)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 897797558) (.leaf 877617759)) (.branch 70 (.leaf 857944211) (.leaf 838761801))) (.branch 73 (.branch 72 (.leaf 820055968) (.leaf 801812685)) (.branch 74 (.leaf 784018431) (.leaf 766660170))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 749725331) (.branch 77 (.leaf 733201790) (.leaf 717077844))) (.branch 80 (.branch 79 (.leaf 701342203) (.leaf 685983962)) (.branch 81 (.leaf 670992594) (.leaf 656357929)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 642070141) (.leaf 628119734)) (.branch 85 (.leaf 614497527) (.leaf 601194645))) (.branch 88 (.branch 87 (.leaf 588202501) (.leaf 575512789)) (.branch 89 (.leaf 563117472) (.leaf 551008771)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 539179155) (.branch 92 (.leaf 527621329) (.leaf 516328229))) (.branch 95 (.branch 94 (.leaf 505293011) (.leaf 494509043)) (.branch 96 (.leaf 483969897) (.leaf 473669340)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 463601329) (.leaf 453760003)) (.branch 100 (.leaf 444139675) (.leaf 434734829))) (.branch 103 (.branch 102 (.leaf 425540109) (.leaf 416550318)) (.branch 104 (.leaf 407760409) (.leaf 399165482))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 390760778) (.leaf 382541671)) (.branch 108 (.leaf 374503670) (.leaf 366642408))) (.branch 111 (.branch 110 (.leaf 358953640) (.leaf 351433243)) (.branch 112 (.leaf 344077202) (.leaf 336881618)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 329842695) (.leaf 322956742)) (.branch 116 (.leaf 316220167) (.leaf 309629474))) (.branch 119 (.branch 118 (.leaf 303181262) (.leaf 296872218)) (.branch 120 (.leaf 290699119) (.leaf 284658824)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 840).prefactor = (5001031888277709/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 840).cutoff/(generalMeanRows 840).c)).2 =
    (7239631046073/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 840).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 840).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 840).q*(generalMeanRows 840).c/2-2 = (1617/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable243.value]
    have hcontinuation : (generalMeanRows 840).q*(generalMeanRows 840).cutoff/2-2 = (3886/1911:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable258.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 840).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 840

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 840).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 840).criticalRate j.val*(generalMeanRows 840).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 840).c*(generalMeanRows 840).criticalPoint j.val)).2-
      (generalMeanRows 840).J/2-(generalMeanRows 840).error (generalMeanGrid j.val)+
      (generalMeanRows 840).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 840).c)).2-
      (generalMeanRows 840).J/2-(generalMeanRows 840).error 4 := by
  have he : (generalMeanRows 840).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 840) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 840)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0840

/-! Kernel-checked entropy margins for general spectral rectangle 841. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0841
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5213963739) (.branch 2 (.leaf 5044649764) (.leaf 4882752841))) (.branch 5 (.branch 4 (.leaf 4727850491) (.leaf 4579550192)) (.branch 6 (.leaf 4437486755) (.leaf 4301319995)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4170732631) (.leaf 4045428415)) (.branch 10 (.leaf 3925130439) (.leaf 3809579611))) (.branch 13 (.branch 12 (.leaf 3698533276) (.leaf 3591763965)) (.branch 14 (.leaf 3489058260) (.leaf 3390215756))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3295048123) (.branch 17 (.leaf 3203378243) (.leaf 3115039416))) (.branch 20 (.branch 19 (.leaf 3029874645) (.leaf 2947735963)) (.branch 21 (.leaf 2868483828) (.leaf 2791986562)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2718119824) (.leaf 2646766142)) (.branch 25 (.leaf 2577814462) (.leaf 2511159744))) (.branch 28 (.branch 27 (.leaf 2446702578) (.leaf 2384348837)) (.branch 29 (.leaf 2324009346) (.leaf 2265599583)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2209039392) (.branch 32 (.leaf 2154252726) (.leaf 2101167397))) (.branch 35 (.branch 34 (.leaf 2049714851) (.leaf 1999829954)) (.branch 36 (.leaf 1951450797) (.leaf 1904518502)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1858977059) (.leaf 1814773157)) (.branch 40 (.leaf 1771856032) (.leaf 1730177328))) (.branch 43 (.branch 42 (.leaf 1689690963) (.leaf 1650353002)) (.branch 44 (.leaf 1612121540) (.leaf 1574956595))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1538820000) (.branch 47 (.leaf 1503675309) (.leaf 1469487706))) (.branch 50 (.branch 49 (.leaf 1436223916) (.leaf 1403852128)) (.branch 51 (.leaf 1372341917) (.leaf 1341664172)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1311791030) (.leaf 1282695809)) (.branch 55 (.leaf 1254352955) (.leaf 1226737978))) (.branch 58 (.branch 57 (.leaf 1199827403) (.leaf 1173598718)) (.branch 59 (.leaf 1148030329) (.leaf 1123101512))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1098792371) (.branch 62 (.leaf 1075083801) (.leaf 1051957445))) (.branch 65 (.branch 64 (.leaf 1029395665) (.leaf 1007381501)) (.branch 66 (.leaf 985898646) (.leaf 964931407)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 944464687) (.leaf 924483948)) (.branch 70 (.leaf 904975191) (.leaf 885924929))) (.branch 73 (.branch 72 (.leaf 867320167) (.leaf 849148375)) (.branch 74 (.leaf 831397473) (.leaf 814055806))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 797112129) (.branch 77 (.leaf 780555587) (.leaf 764375699))) (.branch 80 (.branch 79 (.leaf 748562343) (.leaf 733105738)) (.branch 81 (.leaf 717996433) (.leaf 703225290)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 688783472) (.leaf 674662433)) (.branch 85 (.leaf 660853902) (.leaf 647349874))) (.branch 88 (.branch 87 (.leaf 634142600) (.leaf 621224576)) (.branch 89 (.leaf 608588532) (.leaf 596227424)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 584134424) (.branch 92 (.leaf 572302916) (.leaf 560726481))) (.branch 95 (.branch 94 (.leaf 549398893) (.leaf 538314115)) (.branch 96 (.leaf 527466285) (.leaf 516849714)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 506458879) (.leaf 496288416)) (.branch 100 (.leaf 486333115) (.leaf 476587914))) (.branch 103 (.branch 102 (.leaf 467047893) (.leaf 457708272)) (.branch 104 (.leaf 448564402) (.leaf 439611763))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 430845957) (.leaf 422262709)) (.branch 108 (.leaf 413857857) (.leaf 405627351))) (.branch 111 (.branch 110 (.leaf 397567250) (.leaf 389673715)) (.branch 112 (.leaf 381943011) (.leaf 374371497)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 366955630) (.leaf 359691955)) (.branch 116 (.leaf 352577108) (.leaf 345607809))) (.branch 119 (.branch 118 (.leaf 338780862) (.leaf 332093150)) (.branch 120 (.leaf 325541637) (.leaf 319123358)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 841).prefactor = (4707031035630941/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 841).cutoff/(generalMeanRows 841).c)).2 =
    (399882316673811/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 841).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 841).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 841).q*(generalMeanRows 841).c/2-2 = (77/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable254.value]
    have hcontinuation : (generalMeanRows 841).q*(generalMeanRows 841).cutoff/2-2 = (194/91:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable061.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 841).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 841

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 841).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 841).criticalRate j.val*(generalMeanRows 841).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 841).c*(generalMeanRows 841).criticalPoint j.val)).2-
      (generalMeanRows 841).J/2-(generalMeanRows 841).error (generalMeanGrid j.val)+
      (generalMeanRows 841).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 841).c)).2-
      (generalMeanRows 841).J/2-(generalMeanRows 841).error 4 := by
  have he : (generalMeanRows 841).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 841) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 841)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0841

/-! Kernel-checked entropy margins for general spectral rectangle 842. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0842
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4950744461) (.branch 2 (.leaf 4780899574) (.leaf 4618612458))) (.branch 5 (.branch 4 (.leaf 4463453846) (.leaf 4315024785)) (.branch 6 (.leaf 4172953986) (.leaf 4036895466)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3906526432) (.leaf 3781545386)) (.branch 10 (.leaf 3661670414) (.leaf 3546637651))) (.branch 13 (.branch 12 (.leaf 3436199881) (.leaf 3330125274)) (.branch 14 (.leaf 3228196242) (.leaf 3130208390))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3035969564) (.branch 17 (.leaf 2945298980) (.leaf 2858026426))) (.branch 20 (.branch 19 (.leaf 2773991529) (.leaf 2693043089)) (.branch 21 (.leaf 2615038454) (.leaf 2539842959)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2467329397) (.leaf 2397377534)) (.branch 25 (.leaf 2329873666) (.leaf 2264710202))) (.branch 28 (.branch 27 (.leaf 2201785278) (.leaf 2141002406)) (.branch 29 (.leaf 2082270141) (.leaf 2025501773)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1970615044) (.branch 32 (.leaf 1917531879) (.leaf 1866178141))) (.branch 35 (.branch 34 (.leaf 1816483400) (.leaf 1768380715)) (.branch 36 (.leaf 1721806437) (.leaf 1676700014)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1633003824) (.leaf 1590663004)) (.branch 40 (.leaf 1549625297) (.leaf 1509840911))) (.branch 43 (.branch 42 (.leaf 1471262379) (.leaf 1433844435)) (.branch 44 (.leaf 1397543896) (.leaf 1362319547))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1328132037) (.branch 47 (.leaf 1294943783) (.leaf 1262718871))) (.branch 50 (.branch 49 (.leaf 1231422976) (.leaf 1201023276)) (.branch 51 (.leaf 1171488374) (.leaf 1142788226)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1114894074) (.leaf 1087778377)) (.branch 55 (.leaf 1061414756) (.leaf 1035777929))) (.branch 58 (.branch 57 (.leaf 1010843663) (.leaf 986588721)) (.branch 59 (.leaf 962990810) (.leaf 940028540))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 917681377) (.branch 62 (.leaf 895929604) (.leaf 874754283))) (.branch 65 (.branch 64 (.leaf 854137216) (.leaf 834060911)) (.branch 66 (.leaf 814508550) (.leaf 795463958)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 776911573) (.leaf 758836418)) (.branch 70 (.leaf 741224074) (.leaf 724060655))) (.branch 73 (.branch 72 (.leaf 707332786) (.leaf 691027579)) (.branch 74 (.leaf 675132612) (.leaf 659635907))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 644525912) (.branch 77 (.leaf 629791484) (.leaf 615421868))) (.branch 80 (.branch 79 (.leaf 601406687) (.leaf 587735916)) (.branch 81 (.leaf 574399876) (.leaf 561389218)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 548694904) (.leaf 536308201)) (.branch 85 (.leaf 524220666) (.leaf 512424131))) (.branch 88 (.branch 87 (.leaf 500910699) (.leaf 489672727)) (.branch 89 (.leaf 478702817) (.leaf 467993810)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 457538773) (.branch 92 (.leaf 447330991) (.leaf 437363960))) (.branch 95 (.branch 94 (.leaf 427631377) (.leaf 418127136)) (.branch 96 (.leaf 408845314) (.leaf 399780172)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 390926142) (.leaf 382277824)) (.branch 100 (.leaf 373829979) (.leaf 365577524))) (.branch 103 (.branch 102 (.leaf 357515524) (.leaf 349639189)) (.branch 104 (.leaf 341943868) (.leaf 334425046))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 327078334) (.leaf 319899471)) (.branch 108 (.leaf 312884317) (.leaf 306028847))) (.branch 111 (.branch 110 (.leaf 299329149) (.leaf 292781421)) (.branch 112 (.leaf 286381965) (.leaf 280127187)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 274013588) (.leaf 268037769)) (.branch 116 (.leaf 262196418) (.leaf 256486315))) (.branch 119 (.branch 118 (.leaf 250904327) (.leaf 245447404)) (.branch 120 (.leaf 240112575) (.leaf 234896949)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 842).prefactor = (1192622468680001/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 842).cutoff/(generalMeanRows 842).c)).2 =
    (148564257037/400000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 842).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 842).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 842).q*(generalMeanRows 842).c/2-2 = (17/20:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable055.value]
    have hcontinuation : (generalMeanRows 842).q*(generalMeanRows 842).cutoff/2-2 = (194/91:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable061.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 842).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 842

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 842).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 842).criticalRate j.val*(generalMeanRows 842).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 842).c*(generalMeanRows 842).criticalPoint j.val)).2-
      (generalMeanRows 842).J/2-(generalMeanRows 842).error (generalMeanGrid j.val)+
      (generalMeanRows 842).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 842).c)).2-
      (generalMeanRows 842).J/2-(generalMeanRows 842).error 4 := by
  have he : (generalMeanRows 842).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 842) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 842)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0842

/-! Kernel-checked entropy margins for general spectral rectangle 843. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0843
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5554893725) (.branch 2 (.leaf 5375689213) (.leaf 5204263399))) (.branch 5 (.branch 4 (.leaf 5040177971) (.leaf 4883025477)) (.branch 6 (.leaf 4732426636) (.leaf 4588027926)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4449499435) (.leaf 4316532923)) (.branch 10 (.leaf 4188840095) (.leaf 4066151024))) (.branch 13 (.branch 12 (.leaf 3948212736) (.leaf 3834787931)) (.branch 14 (.leaf 3725653809) (.leaf 3620601012))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3519432654) (.branch 17 (.leaf 3421963437) (.leaf 3328018841))) (.branch 20 (.branch 19 (.leaf 3237434381) (.leaf 3150054924)) (.branch 21 (.leaf 3065734065) (.leaf 2984333546)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2905722726) (.leaf 2829778087)) (.branch 25 (.leaf 2756382781) (.leaf 2685426208))) (.branch 28 (.branch 27 (.leaf 2616803625) (.leaf 2550415787)) (.branch 29 (.leaf 2486168608) (.leaf 2423972851)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2363743835) (.branch 32 (.leaf 2305401165) (.leaf 2248868483))) (.branch 35 (.branch 34 (.leaf 2194073226) (.leaf 2140946415)) (.branch 36 (.leaf 2089422441) (.leaf 2039438879)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1990936307) (.leaf 1943858139)) (.branch 40 (.leaf 1898150464) (.leaf 1853761904))) (.branch 43 (.branch 42 (.leaf 1810643471) (.leaf 1768748438)) (.branch 44 (.leaf 1728032222) (.leaf 1688452263))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1649967918) (.branch 47 (.leaf 1612540363) (.leaf 1576132497))) (.branch 50 (.branch 49 (.leaf 1540708848) (.leaf 1506235495)) (.branch 51 (.leaf 1472679983) (.leaf 1440011254)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1408199569) (.leaf 1377216448)) (.branch 55 (.leaf 1347034605) (.leaf 1317627888))) (.branch 58 (.branch 57 (.leaf 1288971222) (.leaf 1261040561)) (.branch 59 (.leaf 1233812831) (.leaf 1207265889))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1181378474) (.branch 62 (.leaf 1156130168) (.leaf 1131501354))) (.branch 65 (.branch 64 (.leaf 1107473179) (.leaf 1084027518)) (.branch 66 (.leaf 1061146940) (.leaf 1038814677)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1017014590) (.leaf 995731146)) (.branch 70 (.leaf 974949385) (.leaf 954654898))) (.branch 73 (.branch 72 (.leaf 934833800) (.leaf 915472707)) (.branch 74 (.leaf 896558716) (.leaf 878079381))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 860022695) (.branch 77 (.leaf 842377070) (.leaf 825131320))) (.branch 80 (.branch 79 (.leaf 808274641) (.leaf 791796600)) (.branch 81 (.leaf 775687114) (.leaf 759936439)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 744535154) (.leaf 729474148)) (.branch 85 (.leaf 714744608) (.leaf 700338007))) (.branch 88 (.branch 87 (.leaf 686246091) (.leaf 672460870)) (.branch 89 (.leaf 658974604) (.leaf 645779799)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 632869191) (.branch 92 (.leaf 620235741) (.leaf 607872627))) (.branch 95 (.branch 94 (.leaf 595773232) (.leaf 583931138)) (.branch 96 (.leaf 572340119) (.leaf 560994135)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 549887321) (.leaf 539013985)) (.branch 100 (.leaf 528368599) (.leaf 517945794))) (.branch 103 (.branch 102 (.leaf 507740354) (.leaf 497747210)) (.branch 104 (.leaf 487961436) (.leaf 478378243))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 468992975) (.leaf 459801103)) (.branch 108 (.leaf 450798223) (.leaf 441980048))) (.branch 111 (.branch 110 (.leaf 433342408) (.leaf 424881245)) (.branch 112 (.leaf 416592606) (.leaf 408472646)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 400517616) (.leaf 392723869)) (.branch 116 (.leaf 385087848) (.leaf 377606092))) (.branch 119 (.branch 118 (.leaf 370275223) (.leaf 363091953)) (.branch 120 (.leaf 356053075) (.leaf 349155462)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 843).prefactor = (2440349579756931/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 843).cutoff/(generalMeanRows 843).c)).2 =
    (193962839105079/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 843).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 843).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 843).q*(generalMeanRows 843).c/2-2 = (377/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable247.value]
    have hcontinuation : (generalMeanRows 843).q*(generalMeanRows 843).cutoff/2-2 = (5150/2501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable264.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 843).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 843

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 843).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 843).criticalRate j.val*(generalMeanRows 843).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 843).c*(generalMeanRows 843).criticalPoint j.val)).2-
      (generalMeanRows 843).J/2-(generalMeanRows 843).error (generalMeanGrid j.val)+
      (generalMeanRows 843).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 843).c)).2-
      (generalMeanRows 843).J/2-(generalMeanRows 843).error 4 := by
  have he : (generalMeanRows 843).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 843) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 843)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0843

/-! Kernel-checked entropy margins for general spectral rectangle 844. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0844
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5040773050) (.branch 2 (.leaf 4870194113) (.leaf 4707150021))) (.branch 5 (.branch 4 (.leaf 4551214367) (.leaf 4401990809)) (.branch 6 (.leaf 4259110442) (.leaf 4122229459)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3991027050) (.leaf 3865203526)) (.branch 10 (.leaf 3744478623) (.leaf 3628589974))) (.branch 13 (.branch 12 (.leaf 3517291730) (.leaf 3410353304)) (.branch 14 (.leaf 3307558236) (.leaf 3208703156))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3113596841) (.branch 17 (.leaf 3022059348) (.leaf 2933921227))) (.branch 20 (.branch 19 (.leaf 2849022796) (.leaf 2767213476)) (.branch 21 (.leaf 2688351178) (.leaf 2612301740)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2538938408) (.leaf 2468141356)) (.branch 25 (.leaf 2399797243) (.leaf 2333798801))) (.branch 28 (.branch 27 (.leaf 2270044457) (.leaf 2208437976)) (.branch 29 (.leaf 2148888140) (.leaf 2091308438)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2035616784) (.branch 32 (.leaf 1981735257) (.leaf 1929589848))) (.branch 35 (.branch 34 (.leaf 1879110240) (.leaf 1830229587)) (.branch 36 (.leaf 1782884318) (.leaf 1737013949)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1692560909) (.leaf 1649470376)) (.branch 40 (.leaf 1607690125) (.leaf 1567170385))) (.branch 43 (.branch 42 (.leaf 1527863703) (.leaf 1489724818)) (.branch 44 (.leaf 1452710545) (.leaf 1416779661))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1381892804) (.branch 47 (.leaf 1348012370) (.leaf 1315102427))) (.branch 50 (.branch 49 (.leaf 1283128620) (.leaf 1252058099)) (.branch 51 (.leaf 1221859434) (.leaf 1192502545)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1163958636) (.leaf 1136200126)) (.branch 55 (.leaf 1109200594) (.leaf 1082934716))) (.branch 58 (.branch 57 (.leaf 1057378212) (.leaf 1032507800)) (.branch 59 (.leaf 1008301140) (.leaf 984736793))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 961794178) (.branch 62 (.leaf 939453528) (.leaf 917695855))) (.branch 65 (.branch 64 (.leaf 896502911) (.leaf 875857154)) (.branch 66 (.leaf 855741716) (.leaf 836140370)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 817037504) (.leaf 798418089)) (.branch 70 (.leaf 780267657) (.leaf 762572270))) (.branch 73 (.branch 72 (.leaf 745318504) (.leaf 728493419)) (.branch 74 (.leaf 712084542) (.leaf 696079846))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 680467730) (.branch 77 (.leaf 665236999) (.leaf 650376851))) (.branch 80 (.branch 79 (.leaf 635876857) (.leaf 621726945)) (.branch 81 (.leaf 607917386) (.leaf 594438783)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 581282049) (.leaf 568438405)) (.branch 85 (.leaf 555899357) (.leaf 543656692))) (.branch 88 (.branch 87 (.leaf 531702464) (.leaf 520028983)) (.branch 89 (.leaf 508628806) (.leaf 497494725)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 486619762) (.branch 92 (.leaf 475997156) (.leaf 465620357))) (.branch 95 (.branch 94 (.leaf 455483017) (.leaf 445578982)) (.branch 96 (.leaf 435902287) (.leaf 426447146)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 417207947) (.leaf 408179245)) (.branch 100 (.leaf 399355758) (.leaf 390732357))) (.branch 103 (.branch 102 (.leaf 382304064) (.leaf 374066045)) (.branch 104 (.leaf 366013606) (.leaf 358142188))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 350447359) (.leaf 342924817)) (.branch 108 (.leaf 335570376) (.leaf 328379970))) (.branch 111 (.branch 110 (.leaf 321349646) (.leaf 314475558)) (.branch 112 (.leaf 307753967) (.leaf 301181236)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 294753827) (.leaf 288468296)) (.branch 116 (.leaf 282321292) (.leaf 276309555))) (.branch 119 (.branch 118 (.leaf 270429910) (.leaf 264679265)) (.branch 120 (.leaf 259054611) (.leaf 253553016)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 844).prefactor = (2375339260982931/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 844).cutoff/(generalMeanRows 844).c)).2 =
    (46621682431661/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 844).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 844).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 844).q*(generalMeanRows 844).c/2-2 = (83/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable255.value]
    have hcontinuation : (generalMeanRows 844).q*(generalMeanRows 844).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable123.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 844).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 844

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 844).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 844).criticalRate j.val*(generalMeanRows 844).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 844).c*(generalMeanRows 844).criticalPoint j.val)).2-
      (generalMeanRows 844).J/2-(generalMeanRows 844).error (generalMeanGrid j.val)+
      (generalMeanRows 844).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 844).c)).2-
      (generalMeanRows 844).J/2-(generalMeanRows 844).error 4 := by
  have he : (generalMeanRows 844).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 844) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 844)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0844

/-! Kernel-checked entropy margins for general spectral rectangle 845. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0845
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5376535858) (.branch 2 (.leaf 5195826796) (.leaf 5023022810))) (.branch 5 (.branch 4 (.leaf 4857681358) (.leaf 4699390898)) (.branch 6 (.leaf 4547768176) (.leaf 4402455815)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4263120155) (.leaf 4129449313)) (.branch 10 (.leaf 4001151445) (.leaf 3877953169))) (.branch 13 (.branch 12 (.leaf 3759598150) (.leaf 3645845807)) (.branch 14 (.leaf 3536470145) (.leaf 3431258695))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3330011536) (.branch 17 (.leaf 3232540414) (.leaf 3138667925))) (.branch 20 (.branch 19 (.leaf 3048226776) (.leaf 2961059100)) (.branch 21 (.leaf 2877015825) (.leaf 2795956097)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2717746747) (.leaf 2642261795)) (.branch 25 (.leaf 2569381997) (.leaf 2498994421))) (.branch 28 (.branch 27 (.leaf 2430992057) (.leaf 2365273453)) (.branch 29 (.leaf 2301742377) (.leaf 2240307505)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2180882130) (.branch 32 (.leaf 2123383889) (.leaf 2067734507))) (.branch 35 (.branch 34 (.leaf 2013859567) (.leaf 1961688283)) (.branch 36 (.leaf 1911153298) (.leaf 1862190488)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1814738785) (.leaf 1768740004)) (.branch 40 (.leaf 1724138687) (.leaf 1680881954))) (.branch 43 (.branch 42 (.leaf 1638919365) (.leaf 1598202786)) (.branch 44 (.leaf 1558686268) (.leaf 1520325933))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1483079862) (.branch 47 (.leaf 1446907996) (.leaf 1411772038))) (.branch 50 (.branch 49 (.leaf 1377635364) (.leaf 1344462935)) (.branch 51 (.leaf 1312221220) (.leaf 1280878117)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1250402885) (.leaf 1220766071)) (.branch 55 (.leaf 1191939455) (.leaf 1163895980))) (.branch 58 (.branch 57 (.leaf 1136609703) (.leaf 1110055736)) (.branch 59 (.leaf 1084210197) (.leaf 1059050165))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1034553630) (.branch 62 (.leaf 1010699451) (.leaf 987467318))) (.branch 65 (.branch 64 (.leaf 964837708) (.leaf 942791857)) (.branch 66 (.leaf 921311716) (.leaf 900379924)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 879979775) (.leaf 860095189)) (.branch 70 (.leaf 840710684) (.leaf 821811349))) (.branch 73 (.branch 72 (.leaf 803382818) (.leaf 785411248)) (.branch 74 (.leaf 767883295) (.leaf 750786091))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 734107228) (.branch 77 (.leaf 717834732) (.leaf 701957049))) (.branch 80 (.branch 79 (.leaf 686463028) (.leaf 671341899)) (.branch 81 (.leaf 656583263) (.leaf 642177072)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 628113618) (.leaf 614383516)) (.branch 85 (.leaf 600977695) (.leaf 587887380))) (.branch 88 (.branch 87 (.leaf 575104084) (.leaf 562619597)) (.branch 89 (.leaf 550425973) (.leaf 538515517)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 526880784) (.branch 92 (.leaf 515514560) (.leaf 504409858))) (.branch 95 (.branch 94 (.leaf 493559907) (.leaf 482958149)) (.branch 96 (.leaf 472598222) (.leaf 462473961)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 452579386) (.leaf 442908698)) (.branch 100 (.leaf 433456270) (.leaf 424216642))) (.branch 103 (.branch 102 (.leaf 415184514) (.leaf 406354742)) (.branch 104 (.leaf 397722332) (.leaf 389282432))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 381030331) (.leaf 372961452)) (.branch 108 (.leaf 365071347) (.leaf 357355694))) (.branch 111 (.branch 110 (.leaf 349810290) (.leaf 342431053)) (.branch 112 (.leaf 335214009) (.leaf 328155296)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 321251158) (.leaf 314497938)) (.branch 116 (.leaf 307892081) (.leaf 301430126))) (.branch 119 (.branch 118 (.leaf 295108705) (.leaf 288924538)) (.branch 120 (.leaf 282874433) (.leaf 276955282)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 845).prefactor = (985922278471269/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 845).cutoff/(generalMeanRows 845).c)).2 =
    (22541064127997/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 845).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 845).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 845).q*(generalMeanRows 845).c/2-2 = (3259/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable253.value]
    have hcontinuation : (generalMeanRows 845).q*(generalMeanRows 845).cutoff/2-2 = (1921/943:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable260.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 845).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 845

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 845).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 845).criticalRate j.val*(generalMeanRows 845).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 845).c*(generalMeanRows 845).criticalPoint j.val)).2-
      (generalMeanRows 845).J/2-(generalMeanRows 845).error (generalMeanGrid j.val)+
      (generalMeanRows 845).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 845).c)).2-
      (generalMeanRows 845).J/2-(generalMeanRows 845).error 4 := by
  have he : (generalMeanRows 845).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 845) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 845)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0845

/-! Kernel-checked entropy margins for general spectral rectangle 846. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0846
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4958394176) (.branch 2 (.leaf 4786238901) (.leaf 4621725912))) (.branch 5 (.branch 4 (.leaf 4464424880) (.leaf 4313935680)) (.branch 6 (.leaf 4169885758) (.leaf 4031927779)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3899737525) (.leaf 3773012005)) (.branch 10 (.leaf 3651467755) (.leaf 3534839311))) (.branch 13 (.branch 12 (.leaf 3422877817) (.leaf 3315349773)) (.branch 14 (.leaf 3212035890) (.leaf 3112730056))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3017238384) (.branch 17 (.leaf 2925378347) (.leaf 2836977990))) (.branch 20 (.branch 19 (.leaf 2751875196) (.leaf 2669917026)) (.branch 21 (.leaf 2590959100) (.leaf 2514865034)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2441505919) (.leaf 2370759840)) (.branch 25 (.leaf 2302511428) (.leaf 2236651451))) (.branch 28 (.branch 27 (.leaf 2173076432) (.leaf 2111688294)) (.branch 29 (.leaf 2052394029) (.leaf 1995105395)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1939738634) (.branch 32 (.leaf 1886214198) (.leaf 1834456514))) (.branch 35 (.branch 34 (.leaf 1784393742) (.leaf 1735957570)) (.branch 36 (.leaf 1689083005) (.leaf 1643708191)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1599774231) (.leaf 1557225020)) (.branch 40 (.leaf 1516007096) (.leaf 1476069491))) (.branch 43 (.branch 42 (.leaf 1437363600) (.leaf 1399843048)) (.branch 44 (.leaf 1363463577) (.leaf 1328182927))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1293960736) (.branch 47 (.leaf 1260758441) (.leaf 1228539178))) (.branch 50 (.branch 49 (.leaf 1197267704) (.leaf 1166910305)) (.branch 51 (.leaf 1137434725) (.leaf 1108810087)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1081006828) (.leaf 1053996632)) (.branch 55 (.leaf 1027752368) (.leaf 1002248032))) (.branch 58 (.branch 57 (.leaf 977458692) (.leaf 953360436)) (.branch 59 (.leaf 929930323) (.leaf 907146337))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 884987341) (.branch 62 (.leaf 863433038) (.leaf 842463930))) (.branch 65 (.branch 64 (.leaf 822061283) (.leaf 802207087)) (.branch 66 (.leaf 782884028) (.leaf 764075452)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 745765339) (.leaf 727938271)) (.branch 70 (.leaf 710579405) (.leaf 693674451))) (.branch 73 (.branch 72 (.leaf 677209643) (.leaf 661171721)) (.branch 74 (.leaf 645547902) (.leaf 630325868))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 615493739) (.branch 77 (.leaf 601040056) (.leaf 586953764))) (.branch 80 (.branch 79 (.leaf 573224197) (.leaf 559841056)) (.branch 81 (.leaf 546794400) (.leaf 534074627)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 521672462) (.leaf 509578941)) (.branch 85 (.leaf 497785403) (.leaf 486283474))) (.branch 88 (.branch 87 (.leaf 475065057) (.leaf 464122321)) (.branch 89 (.leaf 453447689) (.leaf 443033831)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 432873652) (.branch 92 (.leaf 422960283) (.leaf 413287073))) (.branch 95 (.branch 94 (.leaf 403847583) (.leaf 394635572)) (.branch 96 (.leaf 385644995) (.leaf 376869995)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 368304892) (.leaf 359944183)) (.branch 100 (.leaf 351782528) (.leaf 343814750))) (.branch 103 (.branch 102 (.leaf 336035828) (.leaf 328440889)) (.branch 104 (.leaf 321025205) (.leaf 313784187))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 306713379) (.leaf 299808457)) (.branch 108 (.leaf 293065220) (.leaf 286479589))) (.branch 111 (.branch 110 (.leaf 280047601) (.leaf 273765407)) (.branch 112 (.leaf 267629264) (.leaf 261635538)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 255780694) (.leaf 250061296)) (.branch 116 (.leaf 244474005) (.leaf 239015571))) (.branch 119 (.branch 118 (.leaf 233682837) (.leaf 228472727)) (.branch 120 (.leaf 223382254) (.leaf 218408509)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 846).prefactor = (479606984612167/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 846).cutoff/(generalMeanRows 846).c)).2 =
    (353488536569337/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 846).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 846).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 846).q*(generalMeanRows 846).c/2-2 = (87/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable246.value]
    have hcontinuation : (generalMeanRows 846).q*(generalMeanRows 846).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 846).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 846

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 846).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 846).criticalRate j.val*(generalMeanRows 846).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 846).c*(generalMeanRows 846).criticalPoint j.val)).2-
      (generalMeanRows 846).J/2-(generalMeanRows 846).error (generalMeanGrid j.val)+
      (generalMeanRows 846).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 846).c)).2-
      (generalMeanRows 846).J/2-(generalMeanRows 846).error 4 := by
  have he : (generalMeanRows 846).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 846) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 846)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0846

/-! Kernel-checked entropy margins for general spectral rectangle 847. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0847
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5201137735) (.branch 2 (.leaf 5032591807) (.leaf 4871408679))) (.branch 5 (.branch 4 (.leaf 4717169462) (.leaf 4569484970)) (.branch 6 (.leaf 4427993126) (.leaf 4292356640)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4162260938) (.leaf 4037412295)) (.branch 10 (.leaf 3917536162) (.leaf 3802375655))) (.branch 13 (.branch 12 (.leaf 3691690183) (.leaf 3585254209)) (.branch 14 (.leaf 3482856126) (.leaf 3384297227))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3289390772) (.branch 17 (.leaf 3197961133) (.leaf 3109843011))) (.branch 20 (.branch 19 (.leaf 3024880719) (.leaf 2942927524)) (.branch 21 (.leaf 2863845041) (.leaf 2787502674)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2713777104) (.leaf 2642551814)) (.branch 25 (.leaf 2573716648) (.leaf 2507167409))) (.branch 28 (.branch 27 (.leaf 2442805480) (.leaf 2380537476)) (.branch 29 (.leaf 2320274920) (.leaf 2261933944)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2205435008) (.branch 32 (.leaf 2150702640) (.leaf 2097665194))) (.branch 35 (.branch 34 (.leaf 2046254622) (.leaf 1996406267)) (.branch 36 (.leaf 1948058664) (.leaf 1901153355)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1855634720) (.leaf 1811449813)) (.branch 40 (.leaf 1768548216) (.leaf 1726881893))) (.branch 43 (.branch 42 (.leaf 1686405060) (.leaf 1647074063)) (.branch 44 (.leaf 1608847261) (.leaf 1571684914))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1535549084) (.branch 47 (.leaf 1500403537) (.leaf 1466213656))) (.branch 50 (.branch 49 (.leaf 1432946350) (.leaf 1400569979)) (.branch 51 (.leaf 1369054276) (.leaf 1338370279)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1308490262) (.leaf 1279387670)) (.branch 55 (.leaf 1251037065) (.leaf 1223414066))) (.branch 58 (.branch 57 (.leaf 1196495297) (.leaf 1170258340)) (.branch 59 (.leaf 1144681683) (.leaf 1119744680))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1095427506) (.branch 62 (.leaf 1071711120) (.leaf 1048577225))) (.branch 65 (.branch 64 (.leaf 1026008235) (.leaf 1003987240)) (.branch 66 (.leaf 982497974) (.leaf 961524785)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 941052609) (.leaf 921066940)) (.branch 70 (.leaf 901553806) (.leaf 882499745))) (.branch 73 (.branch 72 (.leaf 863891780) (.leaf 845717401)) (.branch 74 (.leaf 827964540) (.leaf 810621557))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 793677215) (.branch 77 (.leaf 777120667) (.leaf 760941439))) (.branch 80 (.branch 79 (.leaf 745129410) (.leaf 729674802)) (.branch 81 (.leaf 714568165) (.leaf 699800358)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 685362542) (.leaf 671246167)) (.branch 85 (.leaf 657442957) (.leaf 643944900))) (.branch 88 (.branch 87 (.leaf 630744241) (.leaf 617833466)) (.branch 89 (.leaf 605205296) (.leaf 592852677)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 580768774) (.branch 92 (.leaf 568946955) (.leaf 557380793))) (.branch 95 (.branch 94 (.leaf 546064049) (.leaf 534990672)) (.branch 96 (.leaf 524154788) (.leaf 513550696)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 503172858) (.leaf 493015898)) (.branch 100 (.leaf 483074590) (.leaf 473343859))) (.branch 103 (.branch 102 (.leaf 463818772) (.leaf 454494533)) (.branch 104 (.leaf 445366479) (.leaf 436430076))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 427680913) (.leaf 419114698)) (.branch 108 (.leaf 410727257) (.leaf 402514525))) (.branch 111 (.branch 110 (.leaf 394472547) (.leaf 386597470)) (.branch 112 (.leaf 378885545) (.leaf 371333118)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 363936631) (.leaf 356692617)) (.branch 116 (.leaf 349597698) (.leaf 342648581))) (.branch 119 (.branch 118 (.leaf 335842058) (.leaf 329174998)) (.branch 120 (.leaf 322644352) (.leaf 316247144)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 847).prefactor = (4698631908177197/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 847).cutoff/(generalMeanRows 847).c)).2 =
    (24995868186219/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 847).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 847).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 847).q*(generalMeanRows 847).c/2-2 = (6199/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable268.value]
    have hcontinuation : (generalMeanRows 847).q*(generalMeanRows 847).cutoff/2-2 = (1919/897:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable269.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 847).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 847

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 847).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 847).criticalRate j.val*(generalMeanRows 847).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 847).c*(generalMeanRows 847).criticalPoint j.val)).2-
      (generalMeanRows 847).J/2-(generalMeanRows 847).error (generalMeanGrid j.val)+
      (generalMeanRows 847).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 847).c)).2-
      (generalMeanRows 847).J/2-(generalMeanRows 847).error 4 := by
  have he : (generalMeanRows 847).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 847) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 847)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0847

/-! Kernel-checked entropy margins for general spectral rectangle 848. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0848
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5017488975) (.branch 2 (.leaf 4845354287) (.leaf 4680879263))) (.branch 5 (.branch 4 (.leaf 4523628848) (.leaf 4373198709)) (.branch 6 (.leaf 4229212552) (.leaf 4091319730)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3959193098) (.leaf 3832527093)) (.branch 10 (.leaf 3711036002) (.leaf 3594452400))) (.branch 13 (.branch 12 (.leaf 3482525739) (.leaf 3375021065)) (.branch 14 (.leaf 3271717855) (.leaf 3172408959))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3076899633) (.branch 17 (.leaf 2985006654) (.leaf 2896557516))) (.branch 20 (.branch 19 (.leaf 2811389686) (.leaf 2729349921)) (.branch 21 (.leaf 2650293651) (.leaf 2574084392)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2500593222) (.leaf 2429698289)) (.branch 25 (.leaf 2361284353) (.leaf 2295242374))) (.branch 28 (.branch 27 (.leaf 2231469114) (.leaf 2169866785)) (.branch 29 (.leaf 2110342709) (.leaf 2052809006)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1997182309) (.branch 32 (.leaf 1943383492) (.leaf 1891337418))) (.branch 35 (.branch 34 (.leaf 1840972707) (.leaf 1792221516)) (.branch 36 (.leaf 1745019336) (.leaf 1699304802)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1655019512) (.leaf 1612107865)) (.branch 40 (.leaf 1570516900) (.leaf 1530196152))) (.branch 43 (.branch 42 (.leaf 1491097515) (.leaf 1453175114)) (.branch 44 (.leaf 1416385181) (.leaf 1380685948))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1346037532) (.branch 47 (.leaf 1312401842) (.leaf 1279742484))) (.branch 50 (.branch 49 (.leaf 1248024667) (.leaf 1217215127)) (.branch 51 (.leaf 1187282044) (.leaf 1158194969)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1129924755) (.leaf 1102443493)) (.branch 55 (.leaf 1075724444) (.leaf 1049741989))) (.branch 58 (.branch 57 (.leaf 1024471567) (.leaf 999889626)) (.branch 59 (.leaf 975973575) (.leaf 952701734))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 930053293) (.branch 62 (.leaf 908008269) (.leaf 886547469))) (.branch 65 (.branch 64 (.leaf 865652448) (.leaf 845305480)) (.branch 66 (.leaf 825489520) (.leaf 806188175)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 787385672) (.leaf 769066832)) (.branch 70 (.leaf 751217043) (.leaf 733822232))) (.branch 73 (.branch 72 (.leaf 716868843) (.leaf 700343815)) (.branch 74 (.leaf 684234556) (.leaf 668528928))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 653215225) (.branch 77 (.leaf 638282151) (.leaf 623718809))) (.branch 80 (.branch 79 (.leaf 609514679) (.leaf 595659602)) (.branch 81 (.leaf 582143770) (.leaf 568957706)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 556092251) (.leaf 543538554)) (.branch 85 (.leaf 531288058) (.leaf 519332486))) (.branch 88 (.branch 87 (.leaf 507663833) (.leaf 496274354)) (.branch 89 (.leaf 485156551) (.leaf 474303168)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 463707179) (.branch 92 (.leaf 453361778) (.leaf 443260375))) (.branch 95 (.branch 94 (.leaf 433396580) (.leaf 423764205)) (.branch 96 (.leaf 414357249) (.leaf 405169893)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 396196496) (.leaf 387431584)) (.branch 100 (.leaf 378869848) (.leaf 370506135))) (.branch 103 (.branch 102 (.leaf 362335445) (.leaf 354352924)) (.branch 104 (.leaf 346553857) (.leaf 338933668))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 331487910) (.leaf 324212264)) (.branch 108 (.leaf 317102534) (.leaf 310154640))) (.branch 111 (.branch 110 (.leaf 303364618) (.leaf 296728616)) (.branch 112 (.leaf 290242885) (.leaf 283903781)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 277707761) (.leaf 271651377)) (.branch 116 (.leaf 265731274) (.leaf 259944190))) (.branch 119 (.branch 118 (.leaf 254286947) (.leaf 248756455)) (.branch 120 (.leaf 243349703) (.leaf 238063762)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 848).prefactor = (4834804247632419/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 848).cutoff/(generalMeanRows 848).c)).2 =
    (148564257037/400000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 848).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 848).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 848).q*(generalMeanRows 848).c/2-2 = (17/20:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable055.value]
    have hcontinuation : (generalMeanRows 848).q*(generalMeanRows 848).cutoff/2-2 = (194/91:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable061.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 848).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 848

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 848).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 848).criticalRate j.val*(generalMeanRows 848).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 848).c*(generalMeanRows 848).criticalPoint j.val)).2-
      (generalMeanRows 848).J/2-(generalMeanRows 848).error (generalMeanGrid j.val)+
      (generalMeanRows 848).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 848).c)).2-
      (generalMeanRows 848).J/2-(generalMeanRows 848).error 4 := by
  have he : (generalMeanRows 848).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 848) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 848)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0848

/-! Kernel-checked entropy margins for general spectral rectangle 849. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0849
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5003868384) (.branch 2 (.leaf 4829938203) (.leaf 4663780056))) (.branch 5 (.branch 4 (.leaf 4504952689) (.leaf 4353045974)) (.branch 6 (.leaf 4207678199) (.leaf 4068493634)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3935160373) (.leaf 3807368377)) (.branch 10 (.leaf 3684827724) (.leaf 3567267031))) (.branch 13 (.branch 12 (.leaf 3454432018) (.leaf 3346084211)) (.branch 14 (.leaf 3241999767) (.leaf 3141968398))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3045792393) (.branch 17 (.leaf 2953285725) (.leaf 2864273228))) (.branch 20 (.branch 19 (.leaf 2778589853) (.leaf 2696079972)) (.branch 21 (.leaf 2616596747) (.leaf 2540001550)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2466163416) (.leaf 2394958555)) (.branch 25 (.leaf 2326269884) (.leaf 2259986609))) (.branch 28 (.branch 27 (.leaf 2196003827) (.leaf 2134222162)) (.branch 29 (.leaf 2074547422) (.leaf 2016890291)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1961166029) (.branch 32 (.leaf 1907294202) (.leaf 1855198425))) (.branch 35 (.branch 34 (.leaf 1804806130) (.leaf 1756048340)) (.branch 36 (.leaf 1708859462) (.leaf 1663177098)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1618941860) (.leaf 1576097203)) (.branch 40 (.leaf 1534589267) (.leaf 1494366728))) (.branch 43 (.branch 42 (.leaf 1455380657) (.leaf 1417584395)) (.branch 44 (.leaf 1380933423) (.leaf 1345385256))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1310899325) (.branch 47 (.leaf 1277436884) (.leaf 1244960912))) (.branch 50 (.branch 49 (.leaf 1213436018) (.leaf 1182828366)) (.branch 51 (.leaf 1153105587) (.leaf 1124236708)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1096192080) (.leaf 1068943314)) (.branch 55 (.leaf 1042463215) (.leaf 1016725722))) (.branch 58 (.branch 57 (.leaf 991705855) (.leaf 967379663)) (.branch 59 (.leaf 943724168) (.leaf 920717326))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 898337974) (.branch 62 (.leaf 876565795) (.leaf 855381273))) (.branch 65 (.branch 64 (.leaf 834765659) (.leaf 814700932)) (.branch 66 (.leaf 795169768) (.leaf 776155506)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 757642119) (.leaf 739614181)) (.branch 70 (.leaf 722056849) (.leaf 704955826))) (.branch 73 (.branch 72 (.leaf 688297344) (.leaf 672068139)) (.branch 74 (.leaf 656255427) (.leaf 640846885))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 625830629) (.branch 77 (.leaf 611195198) (.leaf 596929534))) (.branch 80 (.branch 79 (.leaf 583022965) (.leaf 569465188)) (.branch 81 (.leaf 556246257) (.leaf 543356562)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 530786823) (.leaf 518528068)) (.branch 85 (.leaf 506571629) (.leaf 494909122))) (.branch 88 (.branch 87 (.leaf 483532440) (.leaf 472433743)) (.branch 89 (.leaf 461605443) (.leaf 451040197)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 440730898) (.branch 92 (.leaf 430670665) (.leaf 420852832))) (.branch 95 (.branch 94 (.leaf 411270945) (.leaf 401918749)) (.branch 96 (.leaf 392790183) (.leaf 383879373)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 375180623) (.leaf 366688410)) (.branch 100 (.leaf 358397379) (.leaf 350302333))) (.branch 103 (.branch 102 (.leaf 342398232) (.leaf 334680183)) (.branch 104 (.leaf 327143439) (.leaf 319783389))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 312595558) (.leaf 305575600)) (.branch 108 (.leaf 298719293) (.leaf 292022536))) (.branch 111 (.branch 110 (.leaf 285481344) (.leaf 279091846)) (.branch 112 (.leaf 272850277) (.leaf 266752980)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 260796397) (.leaf 254977070)) (.branch 116 (.leaf 249291635) (.leaf 243736821))) (.branch 119 (.branch 118 (.leaf 238309446) (.leaf 233006413)) (.branch 120 (.leaf 227824710) (.leaf 222761404)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 849).prefactor = (489998568842921/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 849).cutoff/(generalMeanRows 849).c)).2 =
    (364417607101531/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 849).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 849).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 849).q*(generalMeanRows 849).c/2-2 = (87/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable246.value]
    have hcontinuation : (generalMeanRows 849).q*(generalMeanRows 849).cutoff/2-2 = (194/91:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable061.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 849).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 849

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 849).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 849).criticalRate j.val*(generalMeanRows 849).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 849).c*(generalMeanRows 849).criticalPoint j.val)).2-
      (generalMeanRows 849).J/2-(generalMeanRows 849).error (generalMeanGrid j.val)+
      (generalMeanRows 849).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 849).c)).2-
      (generalMeanRows 849).J/2-(generalMeanRows 849).error 4 := by
  have he : (generalMeanRows 849).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 849) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 849)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0849

/-! Kernel-checked entropy margins for general spectral rectangle 850. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0850
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5185671529) (.branch 2 (.leaf 5015254048) (.leaf 4852309331))) (.branch 5 (.branch 4 (.leaf 4696412608) (.leaf 4547169198)) (.branch 6 (.leaf 4404211880) (.leaf 4267198543)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4135810090) (.leaf 4009748545)) (.branch 10 (.leaf 3888735364) (.leaf 3772509895))) (.branch 13 (.branch 12 (.leaf 3660828000) (.leaf 3553460794)) (.branch 14 (.leaf 3450193505) (.leaf 3350824436))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3255164020) (.branch 17 (.leaf 3163033949) (.leaf 3074266385))) (.branch 20 (.branch 19 (.leaf 2988703236) (.leaf 2906195481)) (.branch 21 (.leaf 2826602568) (.leaf 2749791838)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2675638014) (.leaf 2604022712)) (.branch 25 (.leaf 2534834003) (.leaf 2467965998))) (.branch 28 (.branch 27 (.leaf 2403318470) (.leaf 2340796498)) (.branch 29 (.leaf 2280310142) (.leaf 2221774137)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2165107607) (.branch 32 (.leaf 2110233807) (.leaf 2057079875))) (.branch 35 (.branch 34 (.leaf 2005576601) (.leaf 1955658216)) (.branch 36 (.leaf 1907262190) (.leaf 1860329051)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1814802206) (.leaf 1770627776)) (.branch 40 (.leaf 1727754453) (.leaf 1686133346))) (.branch 43 (.branch 42 (.leaf 1645717855) (.leaf 1606463542)) (.branch 44 (.leaf 1568328015) (.leaf 1531270814))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1495253312) (.branch 47 (.leaf 1460238614) (.leaf 1426191467))) (.branch 50 (.branch 49 (.leaf 1393078174) (.leaf 1360866510)) (.branch 51 (.leaf 1329525650) (.leaf 1299026093)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1269339597) (.leaf 1240439115)) (.branch 55 (.leaf 1212298733) (.leaf 1184893614))) (.branch 58 (.branch 57 (.leaf 1158199945) (.leaf 1132194888)) (.branch 59 (.leaf 1106856529) (.leaf 1082163833))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1058096605) (.branch 62 (.leaf 1034635448) (.leaf 1011761721))) (.branch 65 (.branch 64 (.leaf 989457510) (.leaf 967705589)) (.branch 66 (.leaf 946489390) (.leaf 925792970)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 905600986) (.leaf 885898663)) (.branch 70 (.leaf 866671773) (.leaf 847906605))) (.branch 73 (.branch 72 (.leaf 829589949) (.leaf 811709065)) (.branch 74 (.leaf 794251668) (.leaf 777205908))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 760560348) (.branch 77 (.leaf 744303950) (.leaf 728426053))) (.branch 80 (.branch 79 (.leaf 712916361) (.leaf 697764927)) (.branch 81 (.leaf 682962136) (.leaf 668498695)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 654365614) (.leaf 640554201)) (.branch 85 (.leaf 627056043) (.leaf 613862998))) (.branch 88 (.branch 87 (.leaf 600967185) (.leaf 588360971)) (.branch 89 (.leaf 576036964) (.leaf 563988001)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 552207139) (.branch 92 (.leaf 540687651) (.leaf 529423012))) (.branch 95 (.branch 94 (.leaf 518406894) (.leaf 507633160)) (.branch 96 (.leaf 497095852) (.leaf 486789192)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 476707566) (.leaf 466845528)) (.branch 100 (.leaf 457197785) (.leaf 447759198))) (.branch 103 (.branch 102 (.leaf 438524772) (.leaf 429489654)) (.branch 104 (.leaf 420649127) (.leaf 411998605))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 403533628) (.leaf 395249859)) (.branch 108 (.leaf 387143079) (.leaf 379209184))) (.branch 111 (.branch 110 (.leaf 371444178) (.leaf 363844175)) (.branch 112 (.leaf 356405389) (.leaf 349124137)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 341996830) (.leaf 335019974)) (.branch 116 (.leaf 328190165) (.leaf 321504087))) (.branch 119 (.branch 118 (.leaf 314958509) (.leaf 308550281)) (.branch 120 (.leaf 302276335) (.leaf 296133679)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 850).prefactor = (4761673933131317/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 850).cutoff/(generalMeanRows 850).c)).2 =
    (392841662670013/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 850).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 850).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 850).q*(generalMeanRows 850).c/2-2 = (6357/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable270.value]
    have hcontinuation : (generalMeanRows 850).q*(generalMeanRows 850).cutoff/2-2 = (1919/897:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable269.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 850).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 850

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 850).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 850).criticalRate j.val*(generalMeanRows 850).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 850).c*(generalMeanRows 850).criticalPoint j.val)).2-
      (generalMeanRows 850).J/2-(generalMeanRows 850).error (generalMeanGrid j.val)+
      (generalMeanRows 850).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 850).c)).2-
      (generalMeanRows 850).J/2-(generalMeanRows 850).error 4 := by
  have he : (generalMeanRows 850).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 850) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 850)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0850

/-! Kernel-checked entropy margins for general spectral rectangle 851. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0851
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5170624579) (.branch 2 (.leaf 4998347588) (.leaf 4833654458))) (.branch 5 (.branch 4 (.leaf 4676114431) (.leaf 4525327232)) (.branch 6 (.leaf 4380920403) (.leaf 4242546927)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4109883100) (.leaf 3982626623)) (.branch 10 (.leaf 3860494881) (.leaf 3743223391))) (.branch 13 (.branch 12 (.leaf 3630564402) (.leaf 3522285622)) (.branch 14 (.leaf 3418169062) (.leaf 3318009983))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3221615939) (.branch 17 (.leaf 3128805900) (.leaf 3039409445))) (.branch 20 (.branch 19 (.leaf 2953266034) (.leaf 2870224327)) (.branch 21 (.leaf 2790141565) (.leaf 2712882997)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2638321352) (.leaf 2566336356)) (.branch 25 (.leaf 2496814277) (.leaf 2429647511))) (.branch 28 (.branch 27 (.leaf 2364734198) (.leaf 2301977859)) (.branch 29 (.leaf 2241287071) (.leaf 2182575151)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2125759874) (.branch 32 (.leaf 2070763206) (.leaf 2017511053))) (.branch 35 (.branch 34 (.leaf 1965933028) (.leaf 1915962240)) (.branch 36 (.leaf 1867535085) (.leaf 1820591063)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1775072598) (.leaf 1730924875)) (.branch 40 (.leaf 1688095685) (.leaf 1646535276))) (.branch 43 (.branch 42 (.leaf 1606196226) (.leaf 1567033308)) (.branch 44 (.leaf 1529003374) (.leaf 1492065243))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1456179593) (.branch 47 (.leaf 1421308866) (.leaf 1387417173))) (.branch 50 (.branch 49 (.leaf 1354470207) (.leaf 1322435158)) (.branch 51 (.leaf 1291280642) (.leaf 1260976620)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1231494335) (.leaf 1202806247)) (.branch 55 (.leaf 1174885967) (.leaf 1147708205))) (.branch 58 (.branch 57 (.leaf 1121248713) (.leaf 1095484235)) (.branch 59 (.leaf 1070392454) (.leaf 1045951955))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1022142171) (.branch 62 (.leaf 998943352) (.leaf 976336521))) (.branch 65 (.branch 64 (.leaf 954303436) (.leaf 932826560)) (.branch 66 (.leaf 911889026) (.leaf 891474605)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 871567679) (.leaf 852153209)) (.branch 70 (.leaf 833216715) (.leaf 814744244))) (.branch 73 (.branch 72 (.leaf 796722353) (.leaf 779138080)) (.branch 74 (.leaf 761978929) (.leaf 745232844))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 728888193) (.branch 77 (.leaf 712933751) (.leaf 697358677))) (.branch 80 (.branch 79 (.leaf 682152506) (.leaf 667305125)) (.branch 81 (.leaf 652806763) (.leaf 638647975)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 624819631) (.leaf 611312899)) (.branch 85 (.leaf 598119236) (.leaf 585230375))) (.branch 88 (.branch 87 (.leaf 572638315) (.leaf 560335311)) (.branch 89 (.leaf 548313859) (.leaf 536566695)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 525086777) (.branch 92 (.leaf 513867282) (.leaf 502901597))) (.branch 95 (.branch 94 (.leaf 492183309) (.leaf 481706199)) (.branch 96 (.leaf 471464233) (.leaf 461451559)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 451662495) (.leaf 442091528)) (.branch 100 (.leaf 432733304) (.leaf 423582623))) (.branch 103 (.branch 102 (.leaf 414634437) (.leaf 405883839)) (.branch 104 (.leaf 397326063) (.leaf 388956476))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 380770574) (.leaf 372763980)) (.branch 108 (.leaf 364932434) (.leaf 357271798))) (.branch 111 (.branch 110 (.leaf 349778041) (.leaf 342447246)) (.branch 112 (.leaf 335275599) (.leaf 328259387)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 321394998) (.leaf 314678915)) (.branch 116 (.leaf 308107711) (.leaf 301678053))) (.branch 119 (.branch 118 (.leaf 295386689) (.leaf 289230457)) (.branch 120 (.leaf 283206272) (.leaf 277311130)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 851).prefactor = (482556179938307/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 851).cutoff/(generalMeanRows 851).c)).2 =
    (385799380044601/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 851).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 851).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 851).q*(generalMeanRows 851).c/2-2 = (1303/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable271.value]
    have hcontinuation : (generalMeanRows 851).q*(generalMeanRows 851).cutoff/2-2 = (1919/897:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable269.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 851).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 851

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 851).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 851).criticalRate j.val*(generalMeanRows 851).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 851).c*(generalMeanRows 851).criticalPoint j.val)).2-
      (generalMeanRows 851).J/2-(generalMeanRows 851).error (generalMeanGrid j.val)+
      (generalMeanRows 851).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 851).c)).2-
      (generalMeanRows 851).J/2-(generalMeanRows 851).error 4 := by
  have he : (generalMeanRows 851).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 851) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 851)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0851

/-! Kernel-checked entropy margins for general spectral rectangle 852. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0852
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5193024164) (.branch 2 (.leaf 5024066148) (.leaf 4862526440))) (.branch 5 (.branch 4 (.leaf 4707980021) (.leaf 4560032168)) (.branch 6 (.leaf 4418315804) (.leaf 4282489130)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4152233507) (.leaf 4027251552)) (.branch 10 (.leaf 3907265427) (.leaf 3792015293))) (.branch 13 (.branch 12 (.leaf 3681257908) (.leaf 3574765363)) (.branch 14 (.leaf 3472323930) (.leaf 3373733009))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3278804175) (.branch 17 (.leaf 3187360303) (.leaf 3099234769))) (.branch 20 (.branch 19 (.leaf 3014270712) (.leaf 2932320368)) (.branch 21 (.leaf 2853244446) (.leaf 2776911559)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2703197699) (.leaf 2631985755)) (.branch 25 (.leaf 2563165058) (.leaf 2496630974))) (.branch 28 (.branch 27 (.leaf 2432284517) (.leaf 2370031993)) (.branch 29 (.leaf 2309784670) (.leaf 2251458472)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2194973695) (.branch 32 (.leaf 2140254739) (.leaf 2087229866))) (.branch 35 (.branch 34 (.leaf 2035830964) (.leaf 1985993339)) (.branch 36 (.leaf 1937655508) (.leaf 1890759019)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1845248272) (.leaf 1801070358)) (.branch 40 (.leaf 1758174903) (.leaf 1716513932))) (.branch 43 (.branch 42 (.leaf 1676041727) (.leaf 1636714706)) (.branch 44 (.leaf 1598491307) (.leaf 1561331873))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1525198551) (.branch 47 (.leaf 1490055198) (.leaf 1455867282))) (.branch 50 (.branch 49 (.leaf 1422601804) (.leaf 1390227212)) (.branch 51 (.leaf 1358713329) (.leaf 1328031278)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1298153418) (.leaf 1269053278)) (.branch 55 (.leaf 1240705498) (.leaf 1213085775))) (.branch 58 (.branch 57 (.leaf 1186170808) (.leaf 1159938248)) (.branch 59 (.leaf 1134366652) (.leaf 1109435435))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1085124835) (.branch 62 (.leaf 1061415865) (.leaf 1038290282))) (.branch 65 (.branch 64 (.leaf 1015730548) (.leaf 993719799)) (.branch 66 (.leaf 972241809) (.leaf 951280966)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 930822240) (.leaf 910851154)) (.branch 70 (.leaf 891353765) (.leaf 872316634))) (.branch 73 (.branch 72 (.leaf 853726806) (.leaf 835571788)) (.branch 74 (.leaf 817839527) (.leaf 800518393))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 783597161) (.branch 77 (.leaf 767064988) (.leaf 750911403))) (.branch 80 (.branch 79 (.leaf 735126288) (.leaf 719699864)) (.branch 81 (.leaf 704622676) (.leaf 689885578)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 675479724) (.leaf 661396553)) (.branch 85 (.leaf 647627779) (.leaf 634165378))) (.branch 88 (.branch 87 (.leaf 621001578) (.leaf 608128851)) (.branch 89 (.leaf 595539900) (.leaf 583227653)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 571185253) (.branch 92 (.leaf 559406050) (.leaf 547883592))) (.branch 95 (.branch 94 (.leaf 536611620) (.leaf 525584058)) (.branch 96 (.leaf 514795008) (.leaf 504238743)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 493909700) (.leaf 483802476)) (.branch 100 (.leaf 473911820) (.leaf 464232629))) (.branch 103 (.branch 102 (.leaf 454759941) (.leaf 445488934)) (.branch 104 (.leaf 436414917) (.leaf 427533326))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 418839724) (.leaf 410329790)) (.branch 108 (.leaf 401999321) (.leaf 393844224))) (.branch 111 (.branch 110 (.leaf 385860515) (.leaf 378044314)) (.branch 112 (.leaf 370391842) (.leaf 362899419)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 355563458) (.leaf 348380465)) (.branch 116 (.leaf 341347034) (.leaf 334459845))) (.branch 119 (.branch 118 (.leaf 327715663) (.leaf 321111331)) (.branch 120 (.leaf 314643774) (.leaf 308309991)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 852).prefactor = (2391298771638893/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 852).cutoff/(generalMeanRows 852).c)).2 =
    (408272235896657/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 852).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 852).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 852).q*(generalMeanRows 852).c/2-2 = (1577/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable272.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 852).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 852

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 852).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 852).criticalRate j.val*(generalMeanRows 852).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 852).c*(generalMeanRows 852).criticalPoint j.val)).2-
      (generalMeanRows 852).J/2-(generalMeanRows 852).error (generalMeanGrid j.val)+
      (generalMeanRows 852).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 852).c)).2-
      (generalMeanRows 852).J/2-(generalMeanRows 852).error 4 := by
  have he : (generalMeanRows 852).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 852) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 852)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0852

/-! Kernel-checked entropy margins for general spectral rectangle 853. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0853
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7287348213) (.branch 2 (.leaf 7085564560) (.leaf 6891707675))) (.branch 5 (.branch 4 (.leaf 6705362014) (.leaf 6526140614)) (.branch 6 (.leaf 6353682524) (.leaf 6187650521)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6027729091) (.leaf 5873622619)) (.branch 10 (.leaf 5725053773) (.leaf 5581762056))) (.branch 13 (.branch 12 (.leaf 5443502499) (.leaf 5310044484)) (.branch 14 (.leaf 5181170677) (.leaf 5056676068))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4936367088) (.branch 17 (.leaf 4820060811) (.leaf 4707584228))) (.branch 20 (.branch 19 (.leaf 4598773574) (.leaf 4493473722)) (.branch 21 (.leaf 4391537619) (.leaf 4292825773)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4197205774) (.leaf 4104551858)) (.branch 25 (.leaf 4014744503) (.leaf 3927670049))) (.branch 28 (.branch 27 (.leaf 3843220360) (.leaf 3761292492)) (.branch 29 (.leaf 3681788401) (.leaf 3604614659)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3529682199) (.branch 32 (.leaf 3456906072) (.leaf 3386205219))) (.branch 35 (.branch 34 (.leaf 3317502265) (.leaf 3250723317)) (.branch 36 (.leaf 3185797781) (.leaf 3122658190)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3061240042) (.leaf 3001481646)) (.branch 40 (.leaf 2943323979) (.leaf 2886710555))) (.branch 43 (.branch 42 (.leaf 2831587292) (.leaf 2777902401)) (.branch 44 (.leaf 2725606264) (.leaf 2674651338))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2624992049) (.branch 47 (.leaf 2576584697) (.leaf 2529387372))) (.branch 50 (.branch 49 (.leaf 2483359866) (.leaf 2438463593)) (.branch 51 (.leaf 2394661516) (.leaf 2351918073)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2310199113) (.leaf 2269471826)) (.branch 55 (.leaf 2229704691) (.leaf 2190867407))) (.branch 58 (.branch 57 (.leaf 2152930851) (.leaf 2115867014)) (.branch 59 (.leaf 2079648960) (.leaf 2044250776))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2009647528) (.branch 62 (.leaf 1975815217) (.leaf 1942730742))) (.branch 65 (.branch 64 (.leaf 1910371857) (.leaf 1878717140)) (.branch 66 (.leaf 1847745953) (.leaf 1817438413)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1787775356) (.leaf 1758738312)) (.branch 70 (.leaf 1730309474) (.leaf 1702471667))) (.branch 73 (.branch 72 (.leaf 1675208328) (.leaf 1648503479)) (.branch 74 (.leaf 1622341700) (.leaf 1596708111))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1571588347) (.branch 77 (.leaf 1546968538) (.leaf 1522835291))) (.branch 80 (.branch 79 (.leaf 1499175668) (.leaf 1475977172)) (.branch 81 (.leaf 1453227724) (.leaf 1430915653)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1409029675) (.leaf 1387558880)) (.branch 85 (.leaf 1366492718) (.leaf 1345820984))) (.branch 88 (.branch 87 (.leaf 1325533805) (.leaf 1305621628)) (.branch 89 (.leaf 1286075208) (.leaf 1266885593)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1248044117) (.branch 92 (.leaf 1229542390) (.leaf 1211372283))) (.branch 95 (.branch 94 (.leaf 1193525920) (.leaf 1175995671)) (.branch 96 (.leaf 1158774142) (.leaf 1141854164)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1125228786) (.leaf 1108891269)) (.branch 100 (.leaf 1092835076) (.leaf 1077053865))) (.branch 103 (.branch 102 (.leaf 1061541482) (.leaf 1046291956)) (.branch 104 (.leaf 1031299489) (.leaf 1016558455))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1002063389) (.leaf 987808981)) (.branch 108 (.leaf 973790077) (.leaf 960001666))) (.branch 111 (.branch 110 (.leaf 946438879) (.leaf 933096986)) (.branch 112 (.leaf 919971384) (.leaf 907057601)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 894351287) (.leaf 881848208)) (.branch 116 (.leaf 869544249) (.leaf 857435402))) (.branch 119 (.branch 118 (.leaf 845517768) (.leaf 833787550)) (.branch 120 (.leaf 822241054) (.leaf 810874679)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 853).prefactor = (465923488069613/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 853).cutoff/(generalMeanRows 853).c)).2 =
    (344605219851417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 853).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 853).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 853).q*(generalMeanRows 853).cutoff/2-2 = (20/13:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable273.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 853).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 853

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 853).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 853).criticalRate j.val*(generalMeanRows 853).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 853).c*(generalMeanRows 853).criticalPoint j.val)).2-
      (generalMeanRows 853).J/2-(generalMeanRows 853).error (generalMeanGrid j.val)+
      (generalMeanRows 853).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 853).c)).2-
      (generalMeanRows 853).J/2-(generalMeanRows 853).error 4 := by
  have he : (generalMeanRows 853).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 853) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 853)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0853

/-! Kernel-checked entropy margins for general spectral rectangle 854. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0854
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7523991552) (.branch 2 (.leaf 7312229823) (.leaf 7108798503))) (.branch 5 (.branch 4 (.leaf 6913261553) (.leaf 6725212911)) (.branch 6 (.leaf 6544273788) (.leaf 6370090286)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6202331270) (.leaf 6040686476)) (.branch 10 (.leaf 5884864814) (.leaf 5734592847))) (.branch 13 (.branch 12 (.leaf 5589613424) (.leaf 5449684444)) (.branch 14 (.leaf 5314577740) (.leaf 5184078066))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5057982176) (.branch 17 (.leaf 4936097989) (.leaf 4818243817))) (.branch 20 (.branch 19 (.leaf 4704247676) (.leaf 4593946634)) (.branch 21 (.leaf 4487186233) (.leaf 4383819938)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4283708647) (.leaf 4186720228)) (.branch 25 (.leaf 4092729094) (.leaf 4001615810))) (.branch 28 (.branch 27 (.leaf 3913266730) (.leaf 3827573660)) (.branch 29 (.leaf 3744433541) (.leaf 3663748159)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3585423874) (.branch 32 (.leaf 3509371365) (.leaf 3435505396))) (.branch 35 (.branch 34 (.leaf 3363744590) (.leaf 3294011228)) (.branch 36 (.leaf 3226231051) (.leaf 3160333081)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3096249451) (.leaf 3033915245)) (.branch 40 (.leaf 2973268346) (.leaf 2914249298))) (.branch 43 (.branch 42 (.leaf 2856801174) (.leaf 2800869445)) (.branch 44 (.leaf 2746401869) (.leaf 2693348379))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2641660972) (.branch 47 (.leaf 2591293620) (.leaf 2542202168))) (.branch 50 (.branch 49 (.leaf 2494344251) (.leaf 2447679206)) (.branch 51 (.leaf 2402167998) (.leaf 2357773143)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2314458634) (.leaf 2272189879)) (.branch 55 (.leaf 2230933633) (.leaf 2190657943))) (.branch 58 (.branch 57 (.leaf 2151332082) (.leaf 2112926504)) (.branch 59 (.leaf 2075412784) (.leaf 2038763577))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2002952563) (.branch 62 (.leaf 1967954409) (.leaf 1933744722))) (.branch 65 (.branch 64 (.leaf 1900300014) (.leaf 1867597656)) (.branch 66 (.leaf 1835615851) (.leaf 1804333592)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1773730631) (.leaf 1743787448)) (.branch 70 (.leaf 1714485220) (.leaf 1685805794))) (.branch 73 (.branch 72 (.leaf 1657731657) (.leaf 1630245913)) (.branch 74 (.leaf 1603332255) (.leaf 1576974942))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1551158777) (.branch 77 (.leaf 1525869086) (.leaf 1501091695))) (.branch 80 (.branch 79 (.leaf 1476812913) (.leaf 1453019507)) (.branch 81 (.leaf 1429698693) (.leaf 1406838112)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1384425814) (.leaf 1362450245)) (.branch 85 (.leaf 1340900228) (.leaf 1319764953))) (.branch 88 (.branch 87 (.leaf 1299033959) (.leaf 1278697122)) (.branch 89 (.leaf 1258744643) (.leaf 1239167036)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1219955114) (.branch 92 (.leaf 1201099979) (.leaf 1182593012))) (.branch 95 (.branch 94 (.leaf 1164425864) (.leaf 1146590442)) (.branch 96 (.leaf 1129078901) (.leaf 1111883637)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1094997278) (.leaf 1078412673)) (.branch 100 (.leaf 1062122884) (.leaf 1046121183))) (.branch 103 (.branch 102 (.leaf 1030401039) (.leaf 1014956114)) (.branch 104 (.leaf 999780255) (.leaf 984867489))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 970212014) (.leaf 955808196)) (.branch 108 (.leaf 941650560) (.leaf 927733788))) (.branch 111 (.branch 110 (.leaf 914052710) (.leaf 900602302)) (.branch 112 (.leaf 887377679) (.leaf 874374091)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 861586919) (.leaf 849011668)) (.branch 116 (.leaf 836643966) (.leaf 824479559))) (.branch 119 (.branch 118 (.leaf 812514307) (.leaf 800744178)) (.branch 120 (.leaf 789165248) (.leaf 777773696)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 854).prefactor = (978068251740513/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 854).cutoff/(generalMeanRows 854).c)).2 =
    (20967046018009/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 854).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 854).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 854).q*(generalMeanRows 854).c/2-2 = (53/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable031.value]
    have hcontinuation : (generalMeanRows 854).q*(generalMeanRows 854).cutoff/2-2 = (20/13:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable273.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 854).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 854

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 854).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 854).criticalRate j.val*(generalMeanRows 854).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 854).c*(generalMeanRows 854).criticalPoint j.val)).2-
      (generalMeanRows 854).J/2-(generalMeanRows 854).error (generalMeanGrid j.val)+
      (generalMeanRows 854).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 854).c)).2-
      (generalMeanRows 854).J/2-(generalMeanRows 854).error 4 := by
  have he : (generalMeanRows 854).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 854) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 854)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0854

/-! Kernel-checked entropy margins for general spectral rectangle 855. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0855
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7089824539) (.branch 2 (.leaf 6885753541) (.leaf 6689815242))) (.branch 5 (.branch 4 (.leaf 6501580713) (.leaf 6320650510)) (.branch 6 (.leaf 6146652039) (.leaf 5979237217)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5818080391) (.leaf 5662876482)) (.branch 10 (.leaf 5513339323) (.leaf 5369200160))) (.branch 13 (.branch 12 (.leaf 5230206312) (.leaf 5096119956)) (.branch 14 (.leaf 4966717023) (.leaf 4841786205))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4721128048) (.branch 17 (.leaf 4604554121) (.leaf 4491886265))) (.branch 20 (.branch 19 (.leaf 4382955902) (.leaf 4277603399)) (.branch 21 (.leaf 4175677490) (.leaf 4077034737)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3981539041) (.leaf 3889061185)) (.branch 25 (.leaf 3799478413) (.leaf 3712674044))) (.branch 28 (.branch 27 (.leaf 3628537107) (.leaf 3546962009)) (.branch 29 (.leaf 3467848223) (.leaf 3391100000)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3316626097) (.branch 32 (.leaf 3244339528) (.leaf 3174157328))) (.branch 35 (.branch 34 (.leaf 3106000335) (.leaf 3039792983)) (.branch 36 (.leaf 2975463114) (.leaf 2912941793)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2852163142) (.leaf 2793064185)) (.branch 40 (.leaf 2735584691) (.leaf 2679667045))) (.branch 43 (.branch 42 (.leaf 2625256105) (.leaf 2572299088)) (.branch 44 (.leaf 2520745448) (.leaf 2470546767))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2421656653) (.branch 47 (.leaf 2374030639) (.leaf 2327626095))) (.branch 50 (.branch 49 (.leaf 2282402135) (.leaf 2238319540)) (.branch 51 (.leaf 2195340676) (.leaf 2153429422)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2112551100) (.leaf 2072672406)) (.branch 55 (.leaf 2033761351) (.leaf 1995787199))) (.branch 58 (.branch 57 (.leaf 1958720412) (.leaf 1922532594)) (.branch 59 (.leaf 1887196441) (.leaf 1852685695))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1818975094) (.branch 62 (.leaf 1786040333) (.leaf 1753858016))) (.branch 65 (.branch 64 (.leaf 1722405623) (.leaf 1691661469)) (.branch 66 (.leaf 1661604668) (.leaf 1632215102)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1603473383) (.leaf 1575360827)) (.branch 70 (.leaf 1547859423) (.leaf 1520951806))) (.branch 73 (.branch 72 (.leaf 1494621227) (.leaf 1468851529)) (.branch 74 (.leaf 1443627126) (.leaf 1418932974))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1394754553) (.branch 77 (.leaf 1371077844) (.leaf 1347889311))) (.branch 80 (.branch 79 (.leaf 1325175877) (.leaf 1302924911)) (.branch 81 (.leaf 1281124206) (.leaf 1259761965)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1238826785) (.leaf 1218307638)) (.branch 85 (.leaf 1198193859) (.leaf 1178475135))) (.branch 88 (.branch 87 (.leaf 1159141484) (.leaf 1140183248)) (.branch 89 (.leaf 1121591080) (.leaf 1103355930)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1085469033) (.branch 92 (.leaf 1067921904) (.leaf 1050706320))) (.branch 95 (.branch 94 (.leaf 1033814316) (.leaf 1017238171)) (.branch 96 (.leaf 1000970402) (.leaf 985003755)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 969331195) (.leaf 953945898)) (.branch 100 (.leaf 938841245) (.leaf 924010815))) (.branch 103 (.branch 102 (.leaf 909448374) (.leaf 895147873)) (.branch 104 (.leaf 881103437) (.leaf 867309363))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 853760112) (.leaf 840450301)) (.branch 108 (.leaf 827374702) (.leaf 814528234))) (.branch 111 (.branch 110 (.leaf 801905957) (.leaf 789503070)) (.branch 112 (.leaf 777314903) (.leaf 765336915)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 753564688) (.leaf 741993926)) (.branch 116 (.leaf 730620445) (.leaf 719440175))) (.branch 119 (.branch 118 (.leaf 708449154) (.leaf 697643522)) (.branch 120 (.leaf 687019523) (.leaf 676573497)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 855).prefactor = (601552767906929/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 855).cutoff/(generalMeanRows 855).c)).2 =
    (338975366839347/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 855).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 855).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 855).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 855

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 855).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 855).criticalRate j.val*(generalMeanRows 855).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 855).c*(generalMeanRows 855).criticalPoint j.val)).2-
      (generalMeanRows 855).J/2-(generalMeanRows 855).error (generalMeanGrid j.val)+
      (generalMeanRows 855).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 855).c)).2-
      (generalMeanRows 855).J/2-(generalMeanRows 855).error 4 := by
  have he : (generalMeanRows 855).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 855) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 855)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0855

/-! Kernel-checked entropy margins for general spectral rectangle 856. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0856
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6781415196) (.branch 2 (.leaf 6585592165) (.leaf 6397659006))) (.branch 5 (.branch 4 (.leaf 6217195308) (.leaf 6043809616)) (.branch 6 (.leaf 5877136852) (.leaf 5716836036)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5562588248) (.leaf 5414094806)) (.branch 10 (.leaf 5271075642) (.leaf 5133267832))) (.branch 13 (.branch 12 (.leaf 5000424275) (.leaf 4872312505)) (.branch 14 (.leaf 4748713603) (.leaf 4629421221))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4514240686) (.branch 17 (.leaf 4402988187) (.leaf 4295490029))) (.branch 20 (.branch 19 (.leaf 4191581955) (.leaf 4091108517)) (.branch 21 (.leaf 3993922506) (.leaf 3899884420)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3808861980) (.leaf 3720729679)) (.branch 25 (.leaf 3635368367) (.leaf 3552664864))) (.branch 28 (.branch 27 (.leaf 3472511606) (.leaf 3394806315)) (.branch 29 (.leaf 3319451685) (.leaf 3246355103)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3175428379) (.branch 32 (.leaf 3106587495) (.leaf 3039752379))) (.branch 35 (.branch 34 (.leaf 2974846681) (.leaf 2911797576)) (.branch 36 (.leaf 2850535570) (.leaf 2790994325)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2733110492) (.leaf 2676823552)) (.branch 40 (.leaf 2622075670) (.leaf 2568811559))) (.branch 43 (.branch 42 (.leaf 2516978348) (.leaf 2466525461)) (.branch 44 (.leaf 2417404499) (.leaf 2369569136))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2322975012) (.branch 47 (.leaf 2277579641) (.leaf 2233342316))) (.branch 50 (.branch 49 (.leaf 2190224025) (.leaf 2148187368)) (.branch 51 (.leaf 2107196485) (.leaf 2067216975)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2028215834) (.leaf 1990161387)) (.branch 55 (.leaf 1953023227) (.leaf 1916772156))) (.branch 58 (.branch 57 (.leaf 1881380130) (.leaf 1846820205)) (.branch 59 (.leaf 1813066490) (.leaf 1780094097))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1747879096) (.branch 62 (.leaf 1716398473) (.leaf 1685630092))) (.branch 65 (.branch 64 (.leaf 1655552651) (.leaf 1626145650)) (.branch 66 (.leaf 1597389352) (.leaf 1569264756)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1541753558) (.leaf 1514838125)) (.branch 70 (.leaf 1488501467) (.leaf 1462727209))) (.branch 73 (.branch 72 (.leaf 1437499562) (.leaf 1412803303)) (.branch 74 (.leaf 1388623748) (.leaf 1364946732))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1341758585) (.branch 77 (.leaf 1319046113) (.leaf 1296796579))) (.branch 80 (.branch 79 (.leaf 1274997682) (.leaf 1253637543)) (.branch 81 (.leaf 1232704685) (.leaf 1212188016)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1192076817) (.leaf 1172360725)) (.branch 85 (.leaf 1153029720) (.leaf 1134074108))) (.branch 88 (.branch 87 (.leaf 1115484514) (.leaf 1097251864)) (.branch 89 (.leaf 1079367377) (.leaf 1061822552)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1044609158) (.branch 92 (.leaf 1027719223) (.leaf 1011145023))) (.branch 95 (.branch 94 (.leaf 994879075) (.leaf 978914128)) (.branch 96 (.leaf 963243151) (.leaf 947859328)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 932756048) (.leaf 917926900)) (.branch 100 (.leaf 903365662) (.leaf 889066297))) (.branch 103 (.branch 102 (.leaf 875022944) (.leaf 861229916)) (.branch 104 (.leaf 847681686) (.leaf 834372890))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 821298315) (.leaf 808452895)) (.branch 108 (.leaf 795831709) (.leaf 783429970))) (.branch 111 (.branch 110 (.leaf 771243027) (.leaf 759266354)) (.branch 112 (.leaf 747495552) (.leaf 735926338)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 724554546) (.leaf 713376121)) (.branch 116 (.leaf 702387117) (.leaf 691583689))) (.branch 119 (.branch 118 (.leaf 680962095) (.leaf 670518689)) (.branch 120 (.leaf 660249920) (.leaf 650152327)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 856).prefactor = (2359340191973429/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 856).cutoff/(generalMeanRows 856).c)).2 =
    (176910937478171/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 856).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 856).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 856).q*(generalMeanRows 856).cutoff/2-2 = (5/3:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable274.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 856).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 856

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 856).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 856).criticalRate j.val*(generalMeanRows 856).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 856).c*(generalMeanRows 856).criticalPoint j.val)).2-
      (generalMeanRows 856).J/2-(generalMeanRows 856).error (generalMeanGrid j.val)+
      (generalMeanRows 856).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 856).c)).2-
      (generalMeanRows 856).J/2-(generalMeanRows 856).error 4 := by
  have he : (generalMeanRows 856).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 856) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 856)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0856

/-! Kernel-checked entropy margins for general spectral rectangle 857. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0857
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6028519377) (.branch 2 (.leaf 5828145969) (.leaf 5636094894))) (.branch 5 (.branch 4 (.leaf 5451926556) (.leaf 5275231395)) (.branch 6 (.leaf 5105627221) (.leaf 4942756855)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4786286013) (.leaf 4635901428)) (.branch 10 (.leaf 4491309160) (.leaf 4352233081))) (.branch 13 (.branch 12 (.leaf 4218413505) (.leaf 4089605951)) (.branch 14 (.leaf 3965580030) (.leaf 3846118421))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3731015952) (.branch 17 (.leaf 3620078751) (.leaf 3513123481))) (.branch 20 (.branch 19 (.leaf 3409976633) (.leaf 3310473876)) (.branch 21 (.leaf 3214459464) (.leaf 3121785692)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3032312387) (.leaf 2945906445)) (.branch 25 (.leaf 2862441399) (.leaf 2781797023))) (.branch 28 (.branch 27 (.leaf 2703858957) (.leaf 2628518372)) (.branch 29 (.leaf 2555671643) (.leaf 2485220060)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2417069542) (.branch 32 (.leaf 2351130390) (.leaf 2287317039))) (.branch 35 (.branch 34 (.leaf 2225547834) (.leaf 2165744824)) (.branch 36 (.leaf 2107833558) (.leaf 2051742908)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1997404890) (.leaf 1944754504)) (.branch 40 (.leaf 1893729583) (.leaf 1844270643))) (.branch 43 (.branch 42 (.leaf 1796320759) (.leaf 1749825426)) (.branch 44 (.leaf 1704732446) (.leaf 1660991817))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1618555620) (.branch 47 (.leaf 1577377922) (.leaf 1537414683))) (.branch 50 (.branch 49 (.leaf 1498623662) (.leaf 1460964336)) (.branch 51 (.leaf 1424397818) (.leaf 1388886781)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1354395385) (.leaf 1320889214)) (.branch 55 (.leaf 1288335204) (.leaf 1256701587))) (.branch 58 (.branch 57 (.leaf 1225957832) (.leaf 1196074588)) (.branch 59 (.leaf 1167023633) (.leaf 1138777827))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1111311059) (.branch 62 (.leaf 1084598206) (.leaf 1058615089))) (.branch 65 (.branch 64 (.leaf 1033338435) (.leaf 1008745835)) (.branch 66 (.leaf 984815707) (.leaf 961527265)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 938860482) (.leaf 916796059)) (.branch 70 (.leaf 895315395) (.leaf 874400560))) (.branch 73 (.branch 72 (.leaf 854034264) (.leaf 834199832)) (.branch 74 (.leaf 814881180) (.leaf 796062793))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 777729695) (.branch 77 (.leaf 759867436) (.leaf 742462064))) (.branch 80 (.branch 79 (.leaf 725500111) (.leaf 708968568)) (.branch 81 (.leaf 692854873) (.leaf 677146888)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 661832889) (.leaf 646901541)) (.branch 85 (.leaf 632341892) (.leaf 618143352))) (.branch 88 (.branch 87 (.leaf 604295684) (.leaf 590788986)) (.branch 89 (.leaf 577613681) (.leaf 564760505)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 552220495) (.branch 92 (.leaf 539984975) (.leaf 528045551))) (.branch 95 (.branch 94 (.leaf 516394093) (.leaf 505022735)) (.branch 96 (.leaf 493923855) (.leaf 483090074)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 472514243) (.leaf 462189436)) (.branch 100 (.leaf 452108943) (.leaf 442266259))) (.branch 103 (.branch 102 (.leaf 432655082) (.leaf 423269300)) (.branch 104 (.leaf 414102989) (.leaf 405150402))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 396405968) (.leaf 387864282)) (.branch 108 (.leaf 379520100) (.leaf 371368334))) (.branch 111 (.branch 110 (.leaf 363404047) (.leaf 355622447)) (.branch 112 (.leaf 348018883) (.leaf 340588838)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 333327928) (.leaf 326231896)) (.branch 116 (.leaf 319296605) (.leaf 312518038))) (.branch 119 (.branch 118 (.leaf 305892294) (.leaf 299415579)) (.branch 120 (.leaf 293084210) (.leaf 286894606)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 857).prefactor = (4916144627974013/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 857).cutoff/(generalMeanRows 857).c)).2 =
    (135904361647753/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 857).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 857).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 857).q*(generalMeanRows 857).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 857).q*(generalMeanRows 857).cutoff/2-2 = (5/3:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable274.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 857).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 857

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 857).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 857).criticalRate j.val*(generalMeanRows 857).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 857).c*(generalMeanRows 857).criticalPoint j.val)).2-
      (generalMeanRows 857).J/2-(generalMeanRows 857).error (generalMeanGrid j.val)+
      (generalMeanRows 857).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 857).c)).2-
      (generalMeanRows 857).J/2-(generalMeanRows 857).error 4 := by
  have he : (generalMeanRows 857).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 857) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 857)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0857

/-! Kernel-checked entropy margins for general spectral rectangle 858. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0858
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5873606162) (.branch 2 (.leaf 5681846967) (.leaf 5498090550))) (.branch 5 (.branch 4 (.leaf 5321909356) (.leaf 5152905165)) (.branch 6 (.leaf 4990706504) (.leaf 4834966345)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4685360051) (.leaf 4541583540)) (.branch 10 (.leaf 4403351639) (.leaf 4270396599))) (.branch 13 (.branch 12 (.leaf 4142466762) (.leaf 4019325350)) (.branch 14 (.leaf 3900749372) (.leaf 3786528624))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3676464787) (.branch 17 (.leaf 3570370601) (.leaf 3468069102))) (.branch 20 (.branch 19 (.leaf 3369392939) (.leaf 3274183731)) (.branch 21 (.leaf 3182291488) (.leaf 3093574070)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3007896695) (.leaf 2925131478)) (.branch 25 (.leaf 2845157009) (.leaf 2767857962))) (.branch 28 (.branch 27 (.leaf 2693124728) (.leaf 2620853084)) (.branch 29 (.leaf 2550943874) (.leaf 2483302717)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2417839740) (.branch 32 (.leaf 2354469320) (.leaf 2293109850))) (.branch 35 (.branch 34 (.leaf 2233683516) (.leaf 2176116092)) (.branch 36 (.leaf 2120336745) (.leaf 2066277855)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2013874845) (.leaf 1963066019)) (.branch 40 (.leaf 1913792416) (.leaf 1865997667))) (.branch 43 (.branch 42 (.leaf 1819627863) (.leaf 1774631431)) (.branch 44 (.leaf 1730959016) (.leaf 1688563371))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1647399251) (.branch 47 (.leaf 1607423320) (.leaf 1568594052))) (.branch 50 (.branch 49 (.leaf 1530871647) (.leaf 1494217948)) (.branch 51 (.leaf 1458596359) (.leaf 1423971779)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1390310524) (.leaf 1357580265)) (.branch 55 (.leaf 1325749963) (.leaf 1294789812))) (.branch 58 (.branch 57 (.leaf 1264671182) (.leaf 1235366562)) (.branch 59 (.leaf 1206849516) (.leaf 1179094627))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1152077460) (.branch 62 (.leaf 1125774509) (.leaf 1100163166))) (.branch 65 (.branch 64 (.leaf 1075221672) (.leaf 1050929087)) (.branch 66 (.leaf 1027265252) (.leaf 1004210756)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 981746900) (.leaf 959855673)) (.branch 70 (.leaf 938519720) (.leaf 917722312))) (.branch 73 (.branch 72 (.leaf 897447323) (.leaf 877679203)) (.branch 74 (.leaf 858402956) (.leaf 839604115))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 821268722) (.branch 77 (.leaf 803383305) (.leaf 785934861))) (.branch 80 (.branch 79 (.leaf 768910835) (.leaf 752299104)) (.branch 81 (.leaf 736087956) (.leaf 720266079)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 704822540) (.leaf 689746774)) (.branch 85 (.leaf 675028567) (.leaf 660658043))) (.branch 88 (.branch 87 (.leaf 646625652) (.leaf 632922156)) (.branch 89 (.leaf 619538619) (.leaf 606466393)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 593697107) (.branch 92 (.leaf 581222660) (.leaf 569035208))) (.branch 95 (.branch 94 (.leaf 557127154) (.leaf 545491140)) (.branch 96 (.leaf 534120040) (.leaf 523006946)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 512145166) (.leaf 501528214)) (.branch 100 (.leaf 491149799) (.leaf 481003825))) (.branch 103 (.branch 102 (.leaf 471084377) (.leaf 461385719)) (.branch 104 (.leaf 451902286) (.leaf 442628679))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 433559658) (.leaf 424690137)) (.branch 108 (.leaf 416015177) (.leaf 407529985))) (.branch 111 (.branch 110 (.leaf 399229904) (.leaf 391110414)) (.branch 112 (.leaf 383167121) (.leaf 375395756)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 367792174) (.leaf 360352343)) (.branch 116 (.leaf 353072345) (.leaf 345948372))) (.branch 119 (.branch 118 (.leaf 338976719) (.leaf 332153785)) (.branch 120 (.leaf 325476068) (.leaf 318940159)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 858).prefactor = (4790073063501939/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 858).cutoff/(generalMeanRows 858).c)).2 =
    (302626519837619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 858).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 858).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 858).q*(generalMeanRows 858).c/2-2 = (3051/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable153.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 858).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 858

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 858).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 858).criticalRate j.val*(generalMeanRows 858).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 858).c*(generalMeanRows 858).criticalPoint j.val)).2-
      (generalMeanRows 858).J/2-(generalMeanRows 858).error (generalMeanGrid j.val)+
      (generalMeanRows 858).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 858).c)).2-
      (generalMeanRows 858).J/2-(generalMeanRows 858).error 4 := by
  have he : (generalMeanRows 858).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 858) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 858)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0858

/-! Kernel-checked entropy margins for general spectral rectangle 859. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0859
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5867960500) (.branch 2 (.leaf 5684671914) (.leaf 5509027365))) (.branch 5 (.branch 4 (.leaf 5340612482) (.leaf 5179041537)) (.branch 6 (.leaf 5023954922) (.leaf 4875016906)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4731913638) (.leaf 4594351350)) (.branch 10 (.leaf 4462054752) (.leaf 4334765583))) (.branch 13 (.branch 12 (.leaf 4212241302) (.leaf 4094253909)) (.branch 14 (.leaf 3980588869) (.leaf 3871044139))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3765429275) (.branch 17 (.leaf 3663564627) (.leaf 3565280593))) (.branch 20 (.branch 19 (.leaf 3470416941) (.leaf 3378822185)) (.branch 21 (.leaf 3290353011) (.leaf 3204873748)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3122255885) (.leaf 3042377615)) (.branch 25 (.leaf 2965123424) (.leaf 2890383703))) (.branch 28 (.branch 27 (.leaf 2818054392) (.leaf 2748036649)) (.branch 29 (.leaf 2680236541) (.leaf 2614564757)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2550936340) (.branch 32 (.leaf 2489270442) (.leaf 2429490088))) (.branch 35 (.branch 34 (.leaf 2371521960) (.leaf 2315296194)) (.branch 36 (.leaf 2260746193) (.leaf 2207808444)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2156422357) (.leaf 2106530106)) (.branch 40 (.leaf 2058076480) (.leaf 2011008753))) (.branch 43 (.branch 42 (.leaf 1965276545) (.leaf 1920831709)) (.branch 44 (.leaf 1877628210) (.leaf 1835622023))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1794771026) (.branch 47 (.leaf 1755034908) (.leaf 1716375079))) (.branch 50 (.branch 49 (.leaf 1678754580) (.leaf 1642138012)) (.branch 51 (.leaf 1606491449) (.leaf 1571782374)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1537979610) (.leaf 1505053254)) (.branch 55 (.leaf 1472974617) (.leaf 1441716166))) (.branch 58 (.branch 57 (.leaf 1411251474) (.leaf 1381555161)) (.branch 59 (.leaf 1352602852) (.leaf 1324371128))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1296837481) (.branch 62 (.leaf 1269980275) (.leaf 1243778705))) (.branch 65 (.branch 64 (.leaf 1218212759) (.leaf 1193263185)) (.branch 66 (.leaf 1168911454) (.leaf 1145139731)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1121930841) (.leaf 1099268245)) (.branch 70 (.leaf 1077136006) (.leaf 1055518769))) (.branch 73 (.branch 72 (.leaf 1034401732) (.leaf 1013770625)) (.branch 74 (.leaf 993611684) (.leaf 973911633))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 954657663) (.branch 77 (.leaf 935837410) (.leaf 917438937))) (.branch 80 (.branch 79 (.leaf 899450721) (.leaf 881861630)) (.branch 81 (.leaf 864660908) (.leaf 847838164)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 831383352) (.leaf 815286761)) (.branch 85 (.leaf 799539000) (.leaf 784130983))) (.branch 88 (.branch 87 (.leaf 769053921) (.leaf 754299310)) (.branch 89 (.leaf 739858916) (.leaf 725724767)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 711889144) (.branch 92 (.leaf 698344570) (.leaf 685083800))) (.branch 95 (.branch 94 (.leaf 672099814) (.leaf 659385806)) (.branch 96 (.leaf 646935179) (.leaf 634741535)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 622798669) (.leaf 611100560)) (.branch 100 (.leaf 599641367) (.leaf 588415419))) (.branch 103 (.branch 102 (.leaf 577417213) (.leaf 566641404)) (.branch 104 (.leaf 556082802) (.leaf 545736366))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 535597196) (.leaf 525660533)) (.branch 108 (.leaf 515921751) (.leaf 506376351))) (.branch 111 (.branch 110 (.leaf 497019961) (.leaf 487848328)) (.branch 112 (.leaf 478857314) (.leaf 470042895)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 461401155) (.leaf 452928282)) (.branch 116 (.leaf 444620565) (.leaf 436474394))) (.branch 119 (.branch 118 (.leaf 428486250) (.leaf 420652708)) (.branch 120 (.leaf 412970431) (.leaf 405436168)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 859).prefactor = (4655976769688803/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 859).cutoff/(generalMeanRows 859).c)).2 =
    (86769570602113/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 859).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 859).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 859).q*(generalMeanRows 859).c/2-2 = (1397/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable189.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 859).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 859

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 859).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 859).criticalRate j.val*(generalMeanRows 859).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 859).c*(generalMeanRows 859).criticalPoint j.val)).2-
      (generalMeanRows 859).J/2-(generalMeanRows 859).error (generalMeanGrid j.val)+
      (generalMeanRows 859).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 859).c)).2-
      (generalMeanRows 859).J/2-(generalMeanRows 859).error 4 := by
  have he : (generalMeanRows 859).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 859) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 859)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0859

/-! Kernel-checked entropy margins for general spectral rectangle 860. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0860
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5423797663) (.branch 2 (.leaf 5244138701) (.leaf 5072124505))) (.branch 5 (.branch 4 (.leaf 4907339382) (.leaf 4749396337)) (.branch 6 (.leaf 4597934559) (.leaf 4452617181)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4313129273) (.leaf 4179176053)) (.branch 10 (.leaf 4050481277) (.leaf 3926785788))) (.branch 13 (.branch 12 (.leaf 3807846207) (.leaf 3693433744)) (.branch 14 (.leaf 3583333130) (.leaf 3477341632))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3375268165) (.branch 17 (.leaf 3276932479) (.leaf 3182164411))) (.branch 20 (.branch 19 (.leaf 3090803207) (.leaf 3002696895)) (.branch 21 (.leaf 2917701705) (.leaf 2835681544)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2756507506) (.leaf 2680057415)) (.branch 25 (.leaf 2606215414) (.leaf 2534871576))) (.branch 28 (.branch 27 (.leaf 2465921540) (.leaf 2399266187)) (.branch 29 (.leaf 2334811323) (.leaf 2272467394)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2212149218) (.branch 32 (.leaf 2153775734) (.leaf 2097269770))) (.branch 35 (.branch 34 (.leaf 2042557823) (.leaf 1989569857)) (.branch 36 (.leaf 1938239112) (.leaf 1888501925)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1840297564) (.leaf 1793568070)) (.branch 40 (.leaf 1748258111) (.leaf 1704314841))) (.branch 43 (.branch 42 (.leaf 1661687775) (.leaf 1620328664)) (.branch 44 (.leaf 1580191378) (.leaf 1541231803))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1503407735) (.branch 47 (.leaf 1466678787) (.leaf 1431006296))) (.branch 50 (.branch 49 (.leaf 1396353239) (.leaf 1362684151)) (.branch 51 (.leaf 1329965052) (.leaf 1298163372)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1267247885) (.leaf 1237188644)) (.branch 55 (.leaf 1207956918) (.leaf 1179525141))) (.branch 58 (.branch 57 (.leaf 1151866849) (.leaf 1124956635)) (.branch 59 (.leaf 1098770099) (.leaf 1073283797))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1048475203) (.branch 62 (.leaf 1024322666) (.leaf 1000805368))) (.branch 65 (.branch 64 (.leaf 977903287) (.leaf 955597166)) (.branch 66 (.leaf 933868471) (.leaf 912699367)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 892072683) (.leaf 871971883)) (.branch 70 (.leaf 852381041) (.leaf 833284812))) (.branch 73 (.branch 72 (.leaf 814668408) (.leaf 796517576)) (.branch 74 (.leaf 778818572) (.leaf 761558142))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 744723502) (.branch 77 (.leaf 728302314) (.leaf 712282675))) (.branch 80 (.branch 79 (.leaf 696653090) (.leaf 681402465)) (.branch 81 (.leaf 666520083) (.leaf 651995591)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 637818987) (.leaf 623980606)) (.branch 85 (.leaf 610471102) (.leaf 597281442))) (.branch 88 (.branch 87 (.leaf 584402890) (.leaf 571826993)) (.branch 89 (.leaf 559545576) (.leaf 547550728)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 535834789) (.branch 92 (.leaf 524390346) (.leaf 513210221))) (.branch 95 (.branch 94 (.leaf 502287460) (.leaf 491615329)) (.branch 96 (.leaf 481187302) (.leaf 470997054)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 461038457) (.leaf 451305567)) (.branch 100 (.leaf 441792623) (.leaf 432494036))) (.branch 103 (.branch 102 (.leaf 423404385) (.leaf 414518412)) (.branch 104 (.leaf 405831011) (.leaf 397337230))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 389032260) (.leaf 380911433)) (.branch 108 (.leaf 372970216) (.leaf 365204204))) (.branch 111 (.branch 110 (.leaf 357609121) (.leaf 350180812)) (.branch 112 (.leaf 342915237) (.leaf 335808472)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 328856702) (.leaf 322056217)) (.branch 116 (.leaf 315403413) (.leaf 308894779))) (.branch 119 (.branch 118 (.leaf 302526907) (.leaf 296296475)) (.branch 120 (.leaf 290200257) (.leaf 284235108)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 860).prefactor = (2332035666528919/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 860).cutoff/(generalMeanRows 860).c)).2 =
    (324432505926531/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 860).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 860).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 860).q*(generalMeanRows 860).c/2-2 = (6327/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable234.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 860).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 860

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 860).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 860).criticalRate j.val*(generalMeanRows 860).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 860).c*(generalMeanRows 860).criticalPoint j.val)).2-
      (generalMeanRows 860).J/2-(generalMeanRows 860).error (generalMeanGrid j.val)+
      (generalMeanRows 860).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 860).c)).2-
      (generalMeanRows 860).J/2-(generalMeanRows 860).error 4 := by
  have he : (generalMeanRows 860).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 860) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 860)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0860

/-! Kernel-checked entropy margins for general spectral rectangle 861. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0861
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5467169195) (.branch 2 (.leaf 5296230293) (.leaf 5132530521))) (.branch 5 (.branch 4 (.leaf 4975669552) (.leaf 4825275002)) (.branch 6 (.leaf 4680999980) (.leaf 4542520905)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4409535556) (.leaf 4281761331)) (.branch 10 (.leaf 4158933668) (.leaf 4040804635))) (.branch 13 (.branch 12 (.leaf 3927141651) (.leaf 3817726323)) (.branch 14 (.leaf 3712353399) (.leaf 3610829809))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3512973794) (.branch 17 (.leaf 3418614107) (.leaf 3327589288))) (.branch 20 (.branch 19 (.leaf 3239746991) (.leaf 3154943375)) (.branch 21 (.leaf 3073042538) (.leaf 2993915995)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2917442203) (.leaf 2843506116)) (.branch 25 (.leaf 2771998777) (.leaf 2702816937))) (.branch 28 (.branch 27 (.leaf 2635862705) (.leaf 2571043224)) (.branch 29 (.leaf 2508270363) (.leaf 2447460442)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2388533963) (.branch 32 (.leaf 2331415372) (.leaf 2276032826))) (.branch 35 (.branch 34 (.leaf 2222317983) (.leaf 2170205805)) (.branch 36 (.leaf 2119634368) (.leaf 2070544691)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2022880574) (.leaf 1976588444)) (.branch 40 (.leaf 1931617211) (.leaf 1887918137))) (.branch 43 (.branch 42 (.leaf 1845444709) (.leaf 1804152520)) (.branch 44 (.leaf 1763999158) (.leaf 1724944102))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1686948625) (.branch 47 (.leaf 1649975697) (.leaf 1613989905))) (.branch 50 (.branch 49 (.leaf 1578957365) (.leaf 1544845645)) (.branch 51 (.leaf 1511623695) (.leaf 1479261779)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1447731402) (.leaf 1417005260)) (.branch 55 (.leaf 1387057173) (.leaf 1357862034))) (.branch 58 (.branch 57 (.leaf 1329395757) (.leaf 1301635229)) (.branch 59 (.leaf 1274558259) (.leaf 1248143540))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1222370605) (.branch 62 (.leaf 1197219787) (.leaf 1172672181))) (.branch 65 (.branch 64 (.leaf 1148709612) (.leaf 1125314599)) (.branch 66 (.leaf 1102470323) (.leaf 1080160599)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1058369845) (.leaf 1037083057)) (.branch 70 (.leaf 1016285781) (.leaf 995964090))) (.branch 73 (.branch 72 (.leaf 976104563) (.leaf 956694258)) (.branch 74 (.leaf 937720695) (.leaf 919171833))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 901036056) (.branch 77 (.leaf 883302148) (.leaf 865959283))) (.branch 80 (.branch 79 (.leaf 848997003) (.leaf 832405206)) (.branch 81 (.leaf 816174130) (.leaf 800294338)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 784756707) (.leaf 769552413)) (.branch 85 (.leaf 754672920) (.leaf 740109967))) (.branch 88 (.branch 87 (.leaf 725855560) (.leaf 711901957)) (.branch 89 (.leaf 698241663) (.leaf 684867416)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 671772180) (.branch 92 (.leaf 658949136) (.leaf 646391673))) (.branch 95 (.branch 94 (.leaf 634093383) (.leaf 622048048)) (.branch 96 (.leaf 610249638) (.leaf 598692299)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 587370352) (.leaf 576278283)) (.branch 100 (.leaf 565410737) (.leaf 554762513))) (.branch 103 (.branch 102 (.leaf 544328558) (.leaf 534103964)) (.branch 104 (.leaf 524083959) (.leaf 514263904))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 504639290) (.leaf 495205731)) (.branch 108 (.leaf 485958960) (.leaf 476894826))) (.branch 111 (.branch 110 (.leaf 468009290) (.leaf 459298420)) (.branch 112 (.leaf 450758390) (.leaf 442385473)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 434176039) (.leaf 426126554)) (.branch 116 (.leaf 418233575) (.leaf 410493745))) (.branch 119 (.branch 118 (.leaf 402903795) (.leaf 395460536)) (.branch 120 (.leaf 388160862) (.leaf 381001743)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 861).prefactor = (4513789476004569/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 861).cutoff/(generalMeanRows 861).c)).2 =
    (375784954006769/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 861).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 861).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 861).q*(generalMeanRows 861).c/2-2 = (1427/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable259.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 861).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 861

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 861).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 861).criticalRate j.val*(generalMeanRows 861).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 861).c*(generalMeanRows 861).criticalPoint j.val)).2-
      (generalMeanRows 861).J/2-(generalMeanRows 861).error (generalMeanGrid j.val)+
      (generalMeanRows 861).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 861).c)).2-
      (generalMeanRows 861).J/2-(generalMeanRows 861).error 4 := by
  have he : (generalMeanRows 861).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 861) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 861)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0861

/-! Kernel-checked entropy margins for general spectral rectangle 862. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0862
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5084766409) (.branch 2 (.leaf 4917736110) (.leaf 4757903507))) (.branch 5 (.branch 4 (.leaf 4604869017) (.leaf 4458260964)) (.branch 6 (.leaf 4317733134) (.leaf 4182962603)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4053647791) (.leaf 3929506719)) (.branch 10 (.leaf 3810275436) (.leaf 3695706613))) (.branch 13 (.branch 12 (.leaf 3585568259) (.leaf 3479642562)) (.branch 14 (.leaf 3377724845) (.leaf 3279622599))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3185154622) (.branch 17 (.leaf 3094150211) (.leaf 3006448442))) (.branch 20 (.branch 19 (.leaf 2921897495) (.leaf 2840354045)) (.branch 21 (.leaf 2761682694) (.leaf 2685755452)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2612451259) (.leaf 2541655540)) (.branch 25 (.leaf 2473259796) (.leaf 2407161227))) (.branch 28 (.branch 27 (.leaf 2343262378) (.leaf 2281470813)) (.branch 29 (.leaf 2221698813) (.leaf 2163863095)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2107884550) (.branch 32 (.leaf 2053687995) (.leaf 2001201949))) (.branch 35 (.branch 34 (.leaf 1950358421) (.leaf 1901092709)) (.branch 36 (.leaf 1853343215) (.leaf 1807051273)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1762160985) (.leaf 1718619068)) (.branch 40 (.leaf 1676374714) (.leaf 1635379456))) (.branch 43 (.branch 42 (.leaf 1595587040) (.leaf 1556953308)) (.branch 44 (.leaf 1519436088) (.leaf 1482995091))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1447591809) (.branch 47 (.leaf 1413189428) (.leaf 1379752736))) (.branch 50 (.branch 49 (.leaf 1347248045) (.leaf 1315643114)) (.branch 51 (.leaf 1284907073) (.leaf 1255010357)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1225924641) (.leaf 1197622780)) (.branch 55 (.leaf 1170078748) (.leaf 1143267587))) (.branch 58 (.branch 57 (.leaf 1117165354) (.leaf 1091749070)) (.branch 59 (.leaf 1066996681) (.leaf 1042887006))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1019399700) (.branch 62 (.leaf 996515216) (.leaf 974214765))) (.branch 65 (.branch 64 (.leaf 952480282) (.leaf 931294395)) (.branch 66 (.leaf 910640390) (.leaf 890502184)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 870864293) (.leaf 851711811)) (.branch 70 (.leaf 833030379) (.leaf 814806162))) (.branch 73 (.branch 72 (.leaf 797025829) (.leaf 779676526)) (.branch 74 (.leaf 762745861) (.leaf 746221879))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 730093047) (.branch 77 (.leaf 714348234) (.leaf 698976695))) (.branch 80 (.branch 79 (.leaf 683968054) (.leaf 669312290)) (.branch 81 (.leaf 654999721) (.leaf 641020989)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 627367051) (.leaf 614029161)) (.branch 85 (.leaf 600998863) (.leaf 588267974))) (.branch 88 (.branch 87 (.leaf 575828579) (.leaf 563673014)) (.branch 89 (.leaf 551793863) (.leaf 540183943)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 528836298) (.branch 92 (.leaf 517744187) (.leaf 506901081))) (.branch 95 (.branch 94 (.leaf 496300650) (.leaf 485936758)) (.branch 96 (.leaf 475803455) (.leaf 465894970)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 456205705) (.leaf 446730228)) (.branch 100 (.leaf 437463269) (.leaf 428399710))) (.branch 103 (.branch 102 (.leaf 419534584) (.leaf 410863065)) (.branch 104 (.leaf 402380469) (.leaf 394082243))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 385963964) (.leaf 378021335)) (.branch 108 (.leaf 370250176) (.leaf 362646426))) (.branch 111 (.branch 110 (.leaf 355206135) (.leaf 347925462)) (.branch 112 (.leaf 340800671) (.leaf 333828127)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 327004292) (.leaf 320325725)) (.branch 116 (.leaf 313789074) (.leaf 307391079))) (.branch 119 (.branch 118 (.leaf 301128564) (.leaf 294998436)) (.branch 120 (.leaf 288997683) (.leaf 283123372)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 862).prefactor = (1126014830512147/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 862).cutoff/(generalMeanRows 862).c)).2 =
    (45031595660829/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 862).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 862).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 862).q*(generalMeanRows 862).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 862).q*(generalMeanRows 862).cutoff/2-2 = (2/1:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable275.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 862).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 862

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 862).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 862).criticalRate j.val*(generalMeanRows 862).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 862).c*(generalMeanRows 862).criticalPoint j.val)).2-
      (generalMeanRows 862).J/2-(generalMeanRows 862).error (generalMeanGrid j.val)+
      (generalMeanRows 862).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 862).c)).2-
      (generalMeanRows 862).J/2-(generalMeanRows 862).error 4 := by
  have he : (generalMeanRows 862).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 862) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 862)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0862

/-! Kernel-checked entropy margins for general spectral rectangle 863. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0863
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4961568959) (.branch 2 (.leaf 4790687952) (.leaf 4627289590))) (.branch 5 (.branch 4 (.leaf 4470958746) (.leaf 4321309190)) (.branch 6 (.leaf 4177981061) (.leaf 4040638623)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3908968248) (.leaf 3782676617)) (.branch 10 (.leaf 3661489097) (.leaf 3545148277))) (.branch 13 (.branch 12 (.leaf 3433412648) (.leaf 3326055406)) (.branch 14 (.leaf 3222863363) (.leaf 3123635959))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3028184358) (.branch 17 (.leaf 2936330626) (.leaf 2847906975))) (.branch 20 (.branch 19 (.leaf 2762755071) (.leaf 2680725399)) (.branch 21 (.leaf 2601676683) (.leaf 2525475339)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2451994989) (.leaf 2381115996)) (.branch 25 (.leaf 2312725039) (.leaf 2246714728))) (.branch 28 (.branch 27 (.leaf 2182983230) (.leaf 2121433942)) (.branch 29 (.leaf 2061975166) (.leaf 2004519827)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1948985196) (.branch 32 (.leaf 1895292638) (.leaf 1843367374))) (.branch 35 (.branch 34 (.leaf 1793138266) (.leaf 1744537606)) (.branch 36 (.leaf 1697500925) (.leaf 1651966813)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1607876752) (.leaf 1565174957)) (.branch 40 (.leaf 1523808226) (.leaf 1483725802))) (.branch 43 (.branch 42 (.leaf 1444879247) (.leaf 1407222312)) (.branch 44 (.leaf 1370710828) (.leaf 1335302593))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1300957275) (.branch 47 (.leaf 1267636311) (.leaf 1235302822))) (.branch 50 (.branch 49 (.leaf 1203921523) (.leaf 1173458646)) (.branch 51 (.leaf 1143881862) (.leaf 1115160212)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1087264038) (.leaf 1060164918)) (.branch 55 (.leaf 1033835610) (.leaf 1008249991))) (.branch 58 (.branch 57 (.leaf 983383007) (.leaf 959210616)) (.branch 59 (.leaf 935709748) (.leaf 912858254))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 890634863) (.branch 62 (.leaf 869019143) (.leaf 847991463))) (.branch 65 (.branch 64 (.leaf 827532954) (.leaf 807625475)) (.branch 66 (.leaf 788251580) (.leaf 769394488)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 751038051) (.leaf 733166727)) (.branch 70 (.leaf 715765554) (.leaf 698820124))) (.branch 73 (.branch 72 (.leaf 682316556) (.leaf 666241479)) (.branch 74 (.leaf 650582005) (.leaf 635325710))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 620460614) (.branch 77 (.leaf 605975163) (.leaf 591858210))) (.branch 80 (.branch 79 (.leaf 578098999) (.leaf 564687147)) (.branch 81 (.leaf 551612631) (.leaf 538865773)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 526437222) (.leaf 514317947)) (.branch 85 (.leaf 502499217) (.leaf 490972598))) (.branch 88 (.branch 87 (.leaf 479729930) (.leaf 468763328)) (.branch 89 (.leaf 458065161) (.leaf 447628048)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 437444848) (.branch 92 (.leaf 427508648) (.leaf 417812756))) (.branch 95 (.branch 94 (.leaf 408350692) (.leaf 399116182)) (.branch 96 (.leaf 390103147) (.leaf 381305698)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 372718128) (.leaf 364334907)) (.branch 100 (.leaf 356150671) (.leaf 348160223))) (.branch 103 (.branch 102 (.leaf 340358519) (.leaf 332740670)) (.branch 104 (.leaf 325301932) (.leaf 318037700))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 310943507) (.leaf 304015016)) (.branch 108 (.leaf 297248019) (.leaf 290638426))) (.branch 111 (.branch 110 (.leaf 284182268) (.leaf 277875690)) (.branch 112 (.leaf 271714945) (.leaf 265696395)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 259816504) (.leaf 254071834)) (.branch 116 (.leaf 248459044) (.leaf 242974887))) (.branch 119 (.branch 118 (.leaf 237616204) (.leaf 232379925)) (.branch 120 (.leaf 227263063) (.leaf 222262713)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 863).prefactor = (1159400594592861/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 863).cutoff/(generalMeanRows 863).c)).2 =
    (335560152696259/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 863).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 863).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 863).q*(generalMeanRows 863).c/2-2 = (3421/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable252.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 863).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 863

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 863).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 863).criticalRate j.val*(generalMeanRows 863).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 863).c*(generalMeanRows 863).criticalPoint j.val)).2-
      (generalMeanRows 863).J/2-(generalMeanRows 863).error (generalMeanGrid j.val)+
      (generalMeanRows 863).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 863).c)).2-
      (generalMeanRows 863).J/2-(generalMeanRows 863).error 4 := by
  have he : (generalMeanRows 863).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 863) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 863)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0863

/-! Kernel-checked entropy margins for general spectral rectangle 864. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0864
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5163267915) (.branch 2 (.leaf 4995779992) (.leaf 4835532190))) (.branch 5 (.branch 4 (.leaf 4682118971) (.leaf 4535163268)) (.branch 6 (.leaf 4394314002) (.leaf 4259243855)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4129647289) (.leaf 4005238764)) (.branch 10 (.leaf 3885751132) (.leaf 3770934198))) (.branch 13 (.branch 12 (.leaf 3660553410) (.leaf 3554388673)) (.branch 14 (.leaf 3452233280) (.leaf 3353892927))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3259184824) (.branch 17 (.leaf 3167936880) (.leaf 3079986956))) (.branch 20 (.branch 19 (.leaf 2995182179) (.leaf 2913378319)) (.branch 21 (.leaf 2834439205) (.leaf 2758236197)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2684647696) (.leaf 2613558688)) (.branch 25 (.leaf 2544860327) (.leaf 2478449546))) (.branch 28 (.branch 27 (.leaf 2414228699) (.leaf 2352105228)) (.branch 29 (.leaf 2291991349) (.leaf 2233803771)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2177463422) (.branch 32 (.leaf 2122895204) (.leaf 2070027757))) (.branch 35 (.branch 34 (.leaf 2018793244) (.leaf 1969127149)) (.branch 36 (.leaf 1920968087) (.leaf 1874257626)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1828940122) (.leaf 1784962566)) (.branch 40 (.leaf 1742274437) (.leaf 1700827565))) (.branch 43 (.branch 42 (.leaf 1660576005) (.leaf 1621475916)) (.branch 44 (.leaf 1583485450) (.leaf 1546564644))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1510675323) (.branch 47 (.leaf 1475781004) (.leaf 1441846809))) (.branch 50 (.branch 49 (.leaf 1408839383) (.leaf 1376726817)) (.branch 51 (.leaf 1345478570) (.leaf 1315065403)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1285459314) (.leaf 1256633475)) (.branch 55 (.leaf 1228562175) (.leaf 1201220763))) (.branch 58 (.branch 57 (.leaf 1174585597) (.leaf 1148633998)) (.branch 59 (.leaf 1123344197) (.leaf 1098695298))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1074667232) (.branch 62 (.leaf 1051240721) (.leaf 1028397237))) (.branch 65 (.branch 64 (.leaf 1006118970) (.leaf 984388795)) (.branch 66 (.leaf 963190237) (.leaf 942507444)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 922325160) (.leaf 902628692)) (.branch 70 (.leaf 883403893) (.leaf 864637129))) (.branch 73 (.branch 72 (.leaf 846315265) (.leaf 828425634)) (.branch 74 (.leaf 810956024) (.leaf 793894654))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 777230157) (.branch 77 (.leaf 760951562) (.leaf 745048277))) (.branch 80 (.branch 79 (.leaf 729510071) (.leaf 714327064)) (.branch 81 (.leaf 699489706) (.leaf 684988769)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 670815329) (.leaf 656960756)) (.branch 85 (.leaf 643416702) (.leaf 630175090))) (.branch 88 (.branch 87 (.leaf 617228102) (.leaf 604568169)) (.branch 89 (.leaf 592187961) (.leaf 580080379)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 568238544) (.branch 92 (.leaf 556655790) (.leaf 545325655))) (.branch 95 (.branch 94 (.leaf 534241874) (.leaf 523398370)) (.branch 96 (.leaf 512789250) (.leaf 502408795)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 492251454) (.leaf 482311841)) (.branch 100 (.leaf 472584723) (.leaf 463065021))) (.branch 103 (.branch 102 (.leaf 453747800) (.leaf 444628267)) (.branch 104 (.leaf 435701763) (.leaf 426963760))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 418409855) (.leaf 410035770)) (.branch 108 (.leaf 401837342) (.leaf 393810521))) (.branch 111 (.branch 110 (.leaf 385951368) (.leaf 378256051)) (.branch 112 (.leaf 370720839) (.leaf 363342101)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 356116300) (.leaf 349039995)) (.branch 116 (.leaf 342109833) (.leaf 335322547))) (.branch 119 (.branch 118 (.leaf 328674957) (.leaf 322163961)) (.branch 120 (.leaf 315786538) (.leaf 309539745)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 864).prefactor = (4554164027253597/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 864).cutoff/(generalMeanRows 864).c)).2 =
    (378142330037407/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 864).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 864).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 864).q*(generalMeanRows 864).c/2-2 = (77/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable254.value]
    have hcontinuation : (generalMeanRows 864).q*(generalMeanRows 864).cutoff/2-2 = (190/93:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable276.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 864).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 864

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 864).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 864).criticalRate j.val*(generalMeanRows 864).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 864).c*(generalMeanRows 864).criticalPoint j.val)).2-
      (generalMeanRows 864).J/2-(generalMeanRows 864).error (generalMeanGrid j.val)+
      (generalMeanRows 864).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 864).c)).2-
      (generalMeanRows 864).J/2-(generalMeanRows 864).error 4 := by
  have he : (generalMeanRows 864).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 864) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 864)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0864

/-! Kernel-checked entropy margins for general spectral rectangle 865. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0865
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5160850629) (.branch 2 (.leaf 4991321027) (.leaf 4829096822))) (.branch 5 (.branch 4 (.leaf 4673772452) (.leaf 4524970677)) (.branch 6 (.leaf 4382340106) (.leaf 4245552981)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4114303209) (.leaf 3988304593)) (.branch 10 (.leaf 3867289232) (.leaf 3751006097))) (.branch 13 (.branch 12 (.leaf 3639219723) (.leaf 3531709043)) (.branch 14 (.leaf 3428266313) (.leaf 3328696147))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3232814629) (.branch 17 (.leaf 3140448504) (.leaf 3051434439))) (.branch 20 (.branch 19 (.leaf 2965618342) (.leaf 2882854744)) (.branch 21 (.leaf 2803006220) (.leaf 2725942866)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2651541810) (.leaf 2579686762)) (.branch 25 (.leaf 2510267601) (.leaf 2443179988))) (.branch 28 (.branch 27 (.leaf 2378325009) (.leaf 2315608846)) (.branch 29 (.leaf 2254942468) (.leaf 2196241345)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2139425183) (.branch 32 (.leaf 2084417675) (.leaf 2031146272))) (.branch 35 (.branch 34 (.leaf 1979541964) (.leaf 1929539081)) (.branch 36 (.leaf 1881075104) (.leaf 1834090487)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1788528497) (.leaf 1744335055)) (.branch 40 (.leaf 1701458593) (.leaf 1659849916))) (.branch 43 (.branch 42 (.leaf 1619462079) (.leaf 1580250264)) (.branch 44 (.leaf 1542171668) (.leaf 1505185397))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1469252370) (.branch 47 (.leaf 1434335220) (.leaf 1400398209))) (.branch 50 (.branch 49 (.leaf 1367407146) (.leaf 1335329304)) (.branch 51 (.leaf 1304133355) (.leaf 1273789289)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1244268359) (.leaf 1215543012)) (.branch 55 (.leaf 1187586835) (.leaf 1160374494))) (.branch 58 (.branch 57 (.leaf 1133881688) (.leaf 1108085097)) (.branch 59 (.leaf 1082962333) (.leaf 1058491901))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1034653150) (.branch 62 (.leaf 1011426242) (.leaf 988792105))) (.branch 65 (.branch 64 (.leaf 966732406) (.leaf 945229511)) (.branch 66 (.leaf 924266456) (.leaf 903826918)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 883895183) (.leaf 864456119)) (.branch 70 (.leaf 845495154) (.leaf 826998245))) (.branch 73 (.branch 72 (.leaf 808951861) (.leaf 791342958)) (.branch 74 (.leaf 774158956) (.leaf 757387723))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 741017553) (.branch 77 (.leaf 725037148) (.leaf 709435602))) (.branch 80 (.branch 79 (.leaf 694202384) (.leaf 679327323)) (.branch 81 (.leaf 664800592) (.leaf 650612694)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 636754450) (.leaf 623216984)) (.branch 85 (.leaf 609991711) (.leaf 597070327))) (.branch 88 (.branch 87 (.leaf 584444799) (.leaf 572107349)) (.branch 89 (.leaf 560050448) (.leaf 548266807)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 536749365) (.branch 92 (.leaf 525491281) (.leaf 514485928))) (.branch 95 (.branch 94 (.leaf 503726881) (.leaf 493207912)) (.branch 96 (.leaf 482922982) (.leaf 472866235)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 463031988) (.leaf 453414728)) (.branch 100 (.leaf 444009106) (.leaf 434809927))) (.branch 103 (.branch 102 (.leaf 425812151) (.leaf 417010879)) (.branch 104 (.leaf 408401356) (.leaf 399978962))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 391739208) (.leaf 383677732)) (.branch 108 (.leaf 375790292) (.leaf 368072766))) (.branch 111 (.branch 110 (.leaf 360521145) (.leaf 353131530)) (.branch 112 (.leaf 345900129) (.leaf 338823254)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 331897313) (.leaf 325118813)) (.branch 116 (.leaf 318484353) (.leaf 311990624))) (.branch 119 (.branch 118 (.leaf 305634402) (.leaf 299412548)) (.branch 120 (.leaf 293322005) (.leaf 287359795)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 865).prefactor = (2285727161912603/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 865).cutoff/(generalMeanRows 865).c)).2 =
    (45031595660829/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 865).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 865).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 865).q*(generalMeanRows 865).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 865).q*(generalMeanRows 865).cutoff/2-2 = (2/1:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable275.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 865).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 865

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 865).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 865).criticalRate j.val*(generalMeanRows 865).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 865).c*(generalMeanRows 865).criticalPoint j.val)).2-
      (generalMeanRows 865).J/2-(generalMeanRows 865).error (generalMeanGrid j.val)+
      (generalMeanRows 865).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 865).c)).2-
      (generalMeanRows 865).J/2-(generalMeanRows 865).error 4 := by
  have he : (generalMeanRows 865).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 865) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 865)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0865

/-! Kernel-checked entropy margins for general spectral rectangle 866. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0866
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4995117300) (.branch 2 (.leaf 4824433764) (.leaf 4661193595))) (.branch 5 (.branch 4 (.leaf 4504984216) (.leaf 4355421776)) (.branch 6 (.leaf 4212148640) (.leaf 4074831159)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3943157661) (.leaf 3816836663)) (.branch 10 (.leaf 3695595258) (.leaf 3579177656))) (.branch 13 (.branch 12 (.leaf 3467343876) (.leaf 3359868551)) (.branch 14 (.leaf 3256539847) (.leaf 3157158480))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3061536819) (.branch 17 (.leaf 2969498065) (.leaf 2880875502))) (.branch 20 (.branch 19 (.leaf 2795511807) (.leaf 2713258424)) (.branch 21 (.leaf 2633974975) (.leaf 2557528732)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2483794122) (.leaf 2412652267)) (.branch 25 (.leaf 2343990570) (.leaf 2277702317))) (.branch 28 (.branch 27 (.leaf 2213686320) (.leaf 2151846581)) (.branch 29 (.leaf 2092091979) (.leaf 2034335978)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1978496363) (.branch 32 (.leaf 1924494982) (.leaf 1872257515))) (.branch 35 (.branch 34 (.leaf 1821713253) (.leaf 1772794896)) (.branch 36 (.leaf 1725438360) (.leaf 1679582599)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1635169435) (.leaf 1592143406)) (.branch 40 (.leaf 1550451613) (.leaf 1510043589))) (.branch 43 (.branch 42 (.leaf 1470871160) (.leaf 1432888335)) (.branch 44 (.leaf 1396051181) (.leaf 1360317721))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1325647832) (.branch 47 (.leaf 1292003152) (.leaf 1259346983))) (.branch 50 (.branch 49 (.leaf 1227644215) (.leaf 1196861242)) (.branch 51 (.leaf 1166965888) (.leaf 1137927334)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1109716053) (.leaf 1082303750)) (.branch 55 (.leaf 1055663294) (.leaf 1029768671))) (.branch 58 (.branch 57 (.leaf 1004594921) (.leaf 980118099)) (.branch 59 (.leaf 956315214) (.leaf 933164197))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 910643848) (.branch 62 (.leaf 888733800) (.leaf 867414482))) (.branch 65 (.branch 64 (.leaf 846667078) (.leaf 826473496)) (.branch 66 (.leaf 806816335) (.leaf 787678853)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 769044938) (.leaf 750899078)) (.branch 70 (.leaf 733226339) (.leaf 716012336))) (.branch 73 (.branch 72 (.leaf 699243209) (.leaf 682905603)) (.branch 74 (.leaf 666986644) (.leaf 651473917))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 636355452) (.branch 77 (.leaf 621619699) (.leaf 607255515))) (.branch 80 (.branch 79 (.leaf 593252142) (.leaf 579599198)) (.branch 81 (.leaf 566286656) (.leaf 553304829)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 540644362) (.leaf 528296212)) (.branch 85 (.leaf 516251639) (.leaf 504502195))) (.branch 88 (.branch 87 (.leaf 493039708) (.leaf 481856275)) (.branch 89 (.leaf 470944250) (.leaf 460296236)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 449905070) (.branch 92 (.leaf 439763821) (.leaf 429865777))) (.branch 95 (.branch 94 (.leaf 420204436) (.leaf 410773500)) (.branch 96 (.leaf 401566870) (.leaf 392578631)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 383803052) (.leaf 375234578)) (.branch 100 (.leaf 366867822) (.leaf 358697557))) (.branch 103 (.branch 102 (.leaf 350718716) (.leaf 342926381)) (.branch 104 (.leaf 335315782) (.leaf 327882287))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 320621401) (.leaf 313528759)) (.branch 108 (.leaf 306600124) (.leaf 299831380))) (.branch 111 (.branch 110 (.leaf 293218528) (.leaf 286757684)) (.branch 112 (.leaf 280445075) (.leaf 274277032)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 268249990) (.leaf 262360484)) (.branch 116 (.leaf 256605143) (.leaf 250980692))) (.branch 119 (.branch 118 (.leaf 245483944) (.leaf 240111800)) (.branch 120 (.leaf 234861243) (.leaf 229729341)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 866).prefactor = (4639857768417453/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 866).cutoff/(generalMeanRows 866).c)).2 =
    (338975366839347/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 866).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 866).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 866).q*(generalMeanRows 866).c/2-2 = (17/20:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable055.value]
    have hcontinuation : (generalMeanRows 866).q*(generalMeanRows 866).cutoff/2-2 = (2/1:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable275.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 866).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 866

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 866).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 866).criticalRate j.val*(generalMeanRows 866).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 866).c*(generalMeanRows 866).criticalPoint j.val)).2-
      (generalMeanRows 866).J/2-(generalMeanRows 866).error (generalMeanGrid j.val)+
      (generalMeanRows 866).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 866).c)).2-
      (generalMeanRows 866).J/2-(generalMeanRows 866).error 4 := by
  have he : (generalMeanRows 866).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 866) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 866)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0866

/-! Kernel-checked entropy margins for general spectral rectangle 867. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0867
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5293700410) (.branch 2 (.leaf 5126758638) (.leaf 4967006927))) (.branch 5 (.branch 4 (.leaf 4814040055) (.leaf 4667481376)) (.branch 6 (.leaf 4526980318) (.leaf 4392210159)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4262866028) (.leaf 4138663119)) (.branch 10 (.leaf 4019335079) (.leaf 3904632555))) (.branch 13 (.branch 12 (.leaf 3794321885) (.leaf 3688183905)) (.branch 14 (.leaf 3586012869) (.leaf 3487615465))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3392809919) (.branch 17 (.leaf 3301425173) (.leaf 3213300137))) (.branch 20 (.branch 19 (.leaf 3128283001) (.leaf 3046230602)) (.branch 21 (.leaf 2967007846) (.leaf 2890487169)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2816548048) (.leaf 2745076544)) (.branch 25 (.leaf 2675964879) (.leaf 2609111049))) (.branch 28 (.branch 27 (.leaf 2544418463) (.leaf 2481795604)) (.branch 29 (.leaf 2421155724) (.leaf 2362416550)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2305500016) (.branch 32 (.leaf 2250332015) (.leaf 2196842164))) (.branch 35 (.branch 34 (.leaf 2144963585) (.leaf 2094632703)) (.branch 36 (.leaf 2045789058) (.leaf 1998375125)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1952336148) (.leaf 1907619986)) (.branch 40 (.leaf 1864176969) (.leaf 1821959758))) (.branch 43 (.branch 42 (.leaf 1780923218) (.leaf 1741024302)) (.branch 44 (.leaf 1702221933) (.leaf 1664476902))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1627751766) (.branch 47 (.leaf 1592010757) (.leaf 1557219692))) (.branch 50 (.branch 49 (.leaf 1523345892) (.leaf 1490358102)) (.branch 51 (.leaf 1458226422) (.leaf 1426922232)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1396418131) (.leaf 1366687874)) (.branch 55 (.leaf 1337706314) (.leaf 1309449348))) (.branch 58 (.branch 57 (.leaf 1281893866) (.leaf 1255017700)) (.branch 59 (.leaf 1228799581) (.leaf 1203219090))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1178256626) (.branch 62 (.leaf 1153893356) (.leaf 1130111188))) (.branch 65 (.branch 64 (.leaf 1106892730) (.leaf 1084221260)) (.branch 66 (.leaf 1062080692) (.leaf 1040455551)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1019330939) (.leaf 998692515)) (.branch 70 (.leaf 978526462) (.leaf 958819473))) (.branch 73 (.branch 72 (.leaf 939558719) (.leaf 920731832)) (.branch 74 (.leaf 902326886) (.leaf 884332374))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 866737192) (.branch 77 (.leaf 849530620) (.leaf 832702308))) (.branch 80 (.branch 79 (.leaf 816242257) (.leaf 800140808)) (.branch 81 (.leaf 784388621) (.leaf 768976671)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 753896226) (.leaf 739138841)) (.branch 85 (.leaf 724696342) (.leaf 710560820))) (.branch 88 (.branch 87 (.leaf 696724614) (.leaf 683180306)) (.branch 89 (.leaf 669920710) (.leaf 656938861)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 644228010) (.branch 92 (.leaf 631781611) (.leaf 619593318))) (.branch 95 (.branch 94 (.leaf 607656972) (.leaf 595966601)) (.branch 96 (.leaf 584516405) (.leaf 573300756)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 562314186) (.leaf 551551387)) (.branch 100 (.leaf 541007201) (.leaf 530676616))) (.branch 103 (.branch 102 (.leaf 520554760) (.leaf 510636898)) (.branch 104 (.leaf 500918424) (.leaf 491394859))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 482061846) (.leaf 472915146)) (.branch 108 (.leaf 463950631) (.leaf 455164287))) (.branch 111 (.branch 110 (.leaf 446552202) (.leaf 438110568)) (.branch 112 (.leaf 429835676) (.leaf 421723914)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 413771760) (.leaf 405975784)) (.branch 116 (.leaf 398332643) (.leaf 390839076))) (.branch 119 (.branch 118 (.leaf 383491904) (.leaf 376288029)) (.branch 120 (.leaf 369224426) (.leaf 362298147)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 867).prefactor = (2272903446990357/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 867).cutoff/(generalMeanRows 867).c)).2 =
    (398078889674661/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 867).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 867).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 867).q*(generalMeanRows 867).c/2-2 = (73/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable024.value]
    have hcontinuation : (generalMeanRows 867).q*(generalMeanRows 867).cutoff/2-2 = (382/185:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable277.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 867).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 867

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 867).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 867).criticalRate j.val*(generalMeanRows 867).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 867).c*(generalMeanRows 867).criticalPoint j.val)).2-
      (generalMeanRows 867).J/2-(generalMeanRows 867).error (generalMeanGrid j.val)+
      (generalMeanRows 867).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 867).c)).2-
      (generalMeanRows 867).J/2-(generalMeanRows 867).error 4 := by
  have he : (generalMeanRows 867).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 867) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 867)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0867

/-! Kernel-checked entropy margins for general spectral rectangle 868. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0868
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5244665504) (.branch 2 (.leaf 5076862705) (.leaf 4916312075))) (.branch 5 (.branch 4 (.leaf 4762605329) (.leaf 4615362942)) (.branch 6 (.leaf 4474231639) (.leaf 4338882149)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4209007198) (.leaf 4084319707)) (.branch 10 (.leaf 3964551178) (.leaf 3849450225))) (.branch 13 (.branch 12 (.leaf 3738781259) (.leaf 3632323286)) (.branch 14 (.leaf 3529868825) (.leaf 3431222911))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3336202201) (.branch 17 (.leaf 3244634139) (.leaf 3156356210))) (.branch 20 (.branch 19 (.leaf 3071215245) (.leaf 2989066781)) (.branch 21 (.leaf 2909774485) (.leaf 2833209609)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2759250496) (.leaf 2687782123)) (.branch 25 (.leaf 2618695675) (.leaf 2551888154))) (.branch 28 (.branch 27 (.leaf 2487262015) (.leaf 2424724831)) (.branch 29 (.leaf 2364188976) (.leaf 2305571337)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2248793043) (.branch 32 (.leaf 2193779213) (.leaf 2140458719))) (.branch 35 (.branch 34 (.leaf 2088763970) (.leaf 2038630705)) (.branch 36 (.leaf 1989997804) (.leaf 1942807106)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1897003247) (.leaf 1852533500)) (.branch 40 (.leaf 1809347628) (.leaf 1767397751))) (.branch 43 (.branch 42 (.leaf 1726638210) (.leaf 1687025456)) (.branch 44 (.leaf 1648517926) (.leaf 1611075946))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1574661623) (.branch 47 (.leaf 1539238758) (.leaf 1504772751))) (.branch 50 (.branch 49 (.leaf 1471230522) (.leaf 1438580430)) (.branch 51 (.leaf 1406792202) (.leaf 1375836860)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1345686658) (.leaf 1316315019)) (.branch 55 (.leaf 1287696475) (.leaf 1259806615))) (.branch 58 (.branch 57 (.leaf 1232622032) (.leaf 1206120271)) (.branch 59 (.leaf 1180279788) (.leaf 1155079899))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1130500747) (.branch 62 (.leaf 1106523253) (.leaf 1083129087))) (.branch 65 (.branch 64 (.leaf 1060300631) (.leaf 1038020942)) (.branch 66 (.leaf 1016273723) (.leaf 995043295)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 974314566) (.leaf 954073005)) (.branch 70 (.leaf 934304617) (.leaf 914995917))) (.branch 73 (.branch 72 (.leaf 896133911) (.leaf 877706071)) (.branch 74 (.leaf 859700314) (.leaf 842104986))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 824908840) (.branch 77 (.leaf 808101021) (.leaf 791671045))) (.branch 80 (.branch 79 (.leaf 775608788) (.leaf 759904469)) (.branch 81 (.leaf 744548635) (.leaf 729532147)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 714846168) (.leaf 700482150)) (.branch 85 (.leaf 686431823) (.leaf 672687182))) (.branch 88 (.branch 87 (.leaf 659240479) (.leaf 646084210)) (.branch 89 (.leaf 633211107) (.leaf 620614128)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 608286450) (.branch 92 (.leaf 596221455) (.leaf 584412730))) (.branch 95 (.branch 94 (.leaf 572854053) (.leaf 561539389)) (.branch 96 (.leaf 550462881) (.leaf 539618845)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 529001763) (.leaf 518606276)) (.branch 100 (.leaf 508427179) (.leaf 498459416))) (.branch 103 (.branch 102 (.leaf 488698074) (.leaf 479138377)) (.branch 104 (.leaf 469775683) (.leaf 460605478))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 451623372) (.leaf 442825096)) (.branch 108 (.leaf 434206494) (.leaf 425763524))) (.branch 111 (.branch 110 (.leaf 417492250) (.leaf 409388841)) (.branch 112 (.leaf 401449568) (.leaf 393670798)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 386048993) (.leaf 378580706)) (.branch 116 (.leaf 371262578) (.leaf 364091336))) (.branch 119 (.branch 118 (.leaf 357063791) (.leaf 350176832)) (.branch 120 (.leaf 343427428) (.leaf 336812620)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 868).prefactor = (2288970088125931/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 868).cutoff/(generalMeanRows 868).c)).2 =
    (390779587193049/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 868).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 868).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 868).q*(generalMeanRows 868).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 868).q*(generalMeanRows 868).cutoff/2-2 = (382/185:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable277.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 868).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 868

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 868).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 868).criticalRate j.val*(generalMeanRows 868).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 868).c*(generalMeanRows 868).criticalPoint j.val)).2-
      (generalMeanRows 868).J/2-(generalMeanRows 868).error (generalMeanGrid j.val)+
      (generalMeanRows 868).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 868).c)).2-
      (generalMeanRows 868).J/2-(generalMeanRows 868).error 4 := by
  have he : (generalMeanRows 868).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 868) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 868)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0868

/-! Kernel-checked entropy margins for general spectral rectangle 869. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0869
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5200407280) (.branch 2 (.leaf 5031714617) (.leaf 4870314154))) (.branch 5 (.branch 4 (.leaf 4715797434) (.leaf 4567784679)) (.branch 6 (.leaf 4425922285) (.leaf 4289880579)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4159351826) (.leaf 4034048430)) (.branch 10 (.leaf 3913701324) (.leaf 3798058513))) (.branch 13 (.branch 12 (.leaf 3686883756) (.leaf 3579955377)) (.branch 14 (.leaf 3477065180) (.leaf 3378017465))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3282628128) (.branch 17 (.leaf 3190723838) (.leaf 3102141290))) (.branch 20 (.branch 19 (.leaf 3016726513) (.leaf 2934334237)) (.branch 21 (.leaf 2854827314) (.leaf 2778076179)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2703958356) (.leaf 2632358005)) (.branch 25 (.leaf 2563165497) (.leaf 2496277024))) (.branch 28 (.branch 27 (.leaf 2431594237) (.leaf 2369023911)) (.branch 29 (.leaf 2308477634) (.leaf 2249871513)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2193125908) (.branch 32 (.leaf 2138165180) (.leaf 2084917458))) (.branch 35 (.branch 34 (.leaf 2033314416) (.leaf 1983291073)) (.branch 36 (.leaf 1934785603) (.leaf 1887739153)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1842095681) (.leaf 1797801795)) (.branch 40 (.leaf 1754806610) (.leaf 1713061611))) (.branch 43 (.branch 42 (.leaf 1672520521) (.leaf 1633139186)) (.branch 44 (.leaf 1594875455) (.leaf 1557689078))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1521541605) (.branch 47 (.leaf 1486396290) (.leaf 1452218007))) (.branch 50 (.branch 49 (.leaf 1418973160) (.leaf 1386629608)) (.branch 51 (.leaf 1355156592) (.leaf 1324524663)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1294705617) (.leaf 1265672435)) (.branch 55 (.leaf 1237399218) (.leaf 1209861139))) (.branch 58 (.branch 57 (.leaf 1183034387) (.leaf 1156896118)) (.branch 59 (.leaf 1131424407) (.leaf 1106598209))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1082397309) (.branch 62 (.leaf 1058802291) (.leaf 1035794494))) (.branch 65 (.branch 64 (.leaf 1013355980) (.leaf 991469499)) (.branch 66 (.leaf 970118460) (.leaf 949286896)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 928959441) (.leaf 909121297)) (.branch 70 (.leaf 889758214) (.leaf 870856461))) (.branch 73 (.branch 72 (.leaf 852402807) (.leaf 834384496)) (.branch 74 (.leaf 816789227) (.leaf 799605135))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 782820770) (.branch 77 (.leaf 766425084) (.leaf 750407406))) (.branch 80 (.branch 79 (.leaf 734757434) (.leaf 719465216)) (.branch 81 (.leaf 704521133) (.leaf 689915891)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 675640501) (.leaf 661686272)) (.branch 85 (.leaf 648044796) (.leaf 634707937))) (.branch 88 (.branch 87 (.leaf 621667822) (.leaf 608916826)) (.branch 89 (.leaf 596447567) (.leaf 584252895)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 572325882) (.branch 92 (.leaf 560659813) (.leaf 549248180))) (.branch 95 (.branch 94 (.leaf 538084673) (.leaf 527163173)) (.branch 96 (.leaf 516477741) (.leaf 506022620)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 495792217) (.leaf 485781108)) (.branch 100 (.leaf 475984023) (.leaf 466395845))) (.branch 103 (.branch 102 (.leaf 457011606) (.leaf 447826476)) (.branch 104 (.leaf 438835764) (.leaf 430034908))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 421419476) (.leaf 412985156)) (.branch 108 (.leaf 404727756) (.leaf 396643198))) (.branch 111 (.branch 110 (.leaf 388727515) (.leaf 380976846)) (.branch 112 (.leaf 373387433) (.leaf 365955619)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 358677843) (.leaf 351550639)) (.branch 116 (.leaf 344570628) (.leaf 337734521))) (.branch 119 (.branch 118 (.leaf 331039114) (.leaf 324481285)) (.branch 120 (.leaf 318057990) (.leaf 311766263)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 869).prefactor = (573365263862541/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 869).cutoff/(generalMeanRows 869).c)).2 =
    (378142330037407/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 869).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 869).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 869).q*(generalMeanRows 869).c/2-2 = (77/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable254.value]
    have hcontinuation : (generalMeanRows 869).q*(generalMeanRows 869).cutoff/2-2 = (190/93:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable276.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 869).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 869

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 869).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 869).criticalRate j.val*(generalMeanRows 869).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 869).c*(generalMeanRows 869).criticalPoint j.val)).2-
      (generalMeanRows 869).J/2-(generalMeanRows 869).error (generalMeanGrid j.val)+
      (generalMeanRows 869).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 869).c)).2-
      (generalMeanRows 869).J/2-(generalMeanRows 869).error 4 := by
  have he : (generalMeanRows 869).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 869) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 869)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0869

/-! Kernel-checked entropy margins for general spectral rectangle 870. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0870
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5154019910) (.branch 2 (.leaf 4984505973) (.leaf 4822347188))) (.branch 5 (.branch 4 (.leaf 4667131905) (.leaf 4518477347)) (.branch 6 (.leaf 4376027087) (.leaf 4239448795)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4108432232) (.leaf 3982687437)) (.branch 10 (.leaf 3861943106) (.leaf 3745945127))) (.branch 13 (.branch 12 (.leaf 3634455256) (.leaf 3527249914)) (.branch 14 (.leaf 3424119101) (.leaf 3324865402))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3229303082) (.branch 17 (.leaf 3137257261) (.leaf 3048563155))) (.branch 20 (.branch 19 (.leaf 2963065384) (.leaf 2880617338)) (.branch 21 (.leaf 2801080585) (.leaf 2724324338)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2650224955) (.leaf 2578665476)) (.branch 25 (.leaf 2509535205) (.leaf 2442729314))) (.branch 28 (.branch 27 (.leaf 2378148476) (.leaf 2315698530)) (.branch 29 (.leaf 2255290166) (.leaf 2196838634)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2140263471) (.branch 32 (.leaf 2085488248) (.leaf 2032440336))) (.branch 35 (.branch 34 (.leaf 1981050684) (.leaf 1931253616)) (.branch 36 (.leaf 1882986636) (.leaf 1836190250)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1790807798) (.leaf 1746785299)) (.branch 40 (.leaf 1704071299) (.leaf 1662616737))) (.branch 43 (.branch 42 (.leaf 1622374813) (.leaf 1583300868)) (.branch 44 (.leaf 1545352267) (.leaf 1508488297))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1472670060) (.branch 47 (.leaf 1437860382) (.leaf 1404023722))) (.branch 50 (.branch 49 (.leaf 1371126088) (.leaf 1339134960)) (.branch 51 (.leaf 1308019212) (.leaf 1277749043)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1248295910) (.leaf 1219632469)) (.branch 55 (.leaf 1191732510) (.leaf 1164570906))) (.branch 58 (.branch 57 (.leaf 1138123556) (.leaf 1112367341)) (.branch 59 (.leaf 1087280070) (.leaf 1062840440))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1039027994) (.branch 62 (.leaf 1015823078) (.leaf 993206807))) (.branch 65 (.branch 64 (.leaf 971161024) (.leaf 949668274)) (.branch 66 (.leaf 928711762) (.leaf 908275332)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 888343434) (.leaf 868901093)) (.branch 70 (.leaf 849933891) (.leaf 831427935))) (.branch 73 (.branch 72 (.leaf 813369839) (.leaf 795746699)) (.branch 74 (.leaf 778546072) (.leaf 761755956))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 745364773) (.branch 77 (.leaf 729361348) (.leaf 713734895))) (.branch 80 (.branch 79 (.leaf 698474995) (.leaf 683571590)) (.branch 81 (.leaf 669014957) (.leaf 654795703)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 640904747) (.leaf 627333307)) (.branch 85 (.leaf 614072890) (.leaf 601115280))) (.branch 88 (.branch 87 (.leaf 588452525) (.leaf 576076930)) (.branch 89 (.leaf 563981043) (.leaf 552157647)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 540599752) (.branch 92 (.leaf 529300585) (.leaf 518253584))) (.branch 95 (.branch 94 (.leaf 507452384) (.leaf 496890817)) (.branch 96 (.leaf 486562900) (.leaf 476462829)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 466584974) (.leaf 456923869)) (.branch 100 (.leaf 447474211) (.leaf 438230849))) (.branch 103 (.branch 102 (.leaf 429188784) (.leaf 420343157)) (.branch 104 (.leaf 411689251) (.leaf 403222480))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 394938388) (.leaf 386832646)) (.branch 108 (.leaf 378901041) (.leaf 371139479))) (.branch 111 (.branch 110 (.leaf 363543978) (.leaf 356110664)) (.branch 112 (.leaf 348835768) (.leaf 341715623)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 334746659) (.leaf 327925403)) (.branch 116 (.leaf 321248470) (.leaf 314712568))) (.branch 119 (.branch 118 (.leaf 308314489) (.leaf 302051109)) (.branch 120 (.leaf 295919384) (.leaf 289916348)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 870).prefactor = (2309957911655901/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 870).cutoff/(generalMeanRows 870).c)).2 =
    (185474027201689/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 870).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 870).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 870).q*(generalMeanRows 870).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 870).q*(generalMeanRows 870).cutoff/2-2 = (190/93:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable276.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 870).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 870

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 870).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 870).criticalRate j.val*(generalMeanRows 870).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 870).c*(generalMeanRows 870).criticalPoint j.val)).2-
      (generalMeanRows 870).J/2-(generalMeanRows 870).error (generalMeanGrid j.val)+
      (generalMeanRows 870).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 870).c)).2-
      (generalMeanRows 870).J/2-(generalMeanRows 870).error 4 := by
  have he : (generalMeanRows 870).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 870) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 870)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0870

/-! Kernel-checked entropy margins for general spectral rectangle 871. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0871
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5196479421) (.branch 2 (.leaf 5027845887) (.leaf 4866526727))) (.branch 5 (.branch 4 (.leaf 4712110543) (.leaf 4564214890)) (.branch 6 (.leaf 4422483745) (.leaf 4286585247)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4156209681) (.leaf 4031067664)) (.branch 10 (.leaf 3910888516) (.leaf 3795418787))) (.branch 13 (.branch 12 (.leaf 3684420932) (.leaf 3577672103)) (.branch 14 (.leaf 3474963056) (.leaf 3376097152))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3280889454) (.branch 17 (.leaf 3189165890) (.leaf 3100762502))) (.branch 20 (.branch 19 (.leaf 3015524740) (.leaf 2933306831)) (.branch 21 (.leaf 2853971183) (.leaf 2777387853)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2703434037) (.leaf 2631993616)) (.branch 25 (.leaf 2562956727) (.leaf 2496219369))) (.branch 28 (.branch 27 (.leaf 2431683037) (.leaf 2369254381)) (.branch 29 (.leaf 2308844894) (.leaf 2250370618)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2193751870) (.branch 32 (.leaf 2138912989) (.leaf 2085782101))) (.branch 35 (.branch 34 (.leaf 2034290897) (.leaf 1984374428)) (.branch 36 (.leaf 1935970911) (.leaf 1889021552)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1843470373) (.leaf 1799264061)) (.branch 40 (.leaf 1756351817) (.leaf 1714685214))) (.branch 43 (.branch 42 (.leaf 1674218076) (.leaf 1634906349)) (.branch 44 (.leaf 1596707989) (.leaf 1559582858))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1523492617) (.branch 47 (.leaf 1488400636) (.leaf 1454271902))) (.branch 50 (.branch 49 (.leaf 1421072939) (.leaf 1388771723)) (.branch 51 (.leaf 1357337613) (.leaf 1326741276)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1296954626) (.leaf 1267950758)) (.branch 55 (.leaf 1239703890) (.leaf 1212189307))) (.branch 58 (.branch 57 (.leaf 1185383309) (.leaf 1159263163)) (.branch 59 (.leaf 1133807051) (.leaf 1108994033))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1084804000) (.branch 62 (.leaf 1061217634) (.leaf 1038216375))) (.branch 65 (.branch 64 (.leaf 1015782381) (.leaf 993898497)) (.branch 66 (.leaf 972548222) (.leaf 951715679)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 931385586) (.leaf 911543232)) (.branch 70 (.leaf 892174447) (.leaf 873265579))) (.branch 73 (.branch 72 (.leaf 854803472) (.leaf 836775446)) (.branch 74 (.leaf 819169269) (.leaf 801973146))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 785175693) (.branch 77 (.leaf 768765926) (.leaf 752733236))) (.branch 80 (.branch 79 (.leaf 737067380) (.leaf 721758463)) (.branch 81 (.leaf 706796921) (.leaf 692173513)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 677879301) (.leaf 663905642)) (.branch 85 (.leaf 650244175) (.leaf 636886809))) (.branch 88 (.branch 87 (.leaf 623825713) (.leaf 611053303)) (.branch 89 (.leaf 598562237) (.leaf 586345402)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 574395905) (.branch 92 (.leaf 562707067) (.leaf 551272411))) (.branch 95 (.branch 94 (.leaf 540085659) (.leaf 529140720)) (.branch 96 (.leaf 518431686) (.leaf 507952824)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 497698568) (.leaf 487663518)) (.branch 100 (.leaf 477842426) (.leaf 468230199))) (.branch 103 (.branch 102 (.leaf 458821887) (.leaf 449612682)) (.branch 104 (.leaf 440597908) (.leaf 431773025))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 423133613) (.leaf 414675379)) (.branch 108 (.leaf 406394144) (.leaf 398285844))) (.branch 111 (.branch 110 (.leaf 390346524) (.leaf 382572336)) (.branch 112 (.leaf 374959534) (.leaf 367504472)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 360203597) (.leaf 353053453)) (.branch 116 (.leaf 346050670) (.leaf 339191967))) (.branch 119 (.branch 118 (.leaf 332474147) (.leaf 325894095)) (.branch 120 (.leaf 319448773) (.leaf 313135221)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 871).prefactor = (4610300601438147/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 871).cutoff/(generalMeanRows 871).c)).2 =
    (191766589336141/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 871).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 871).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 871).q*(generalMeanRows 871).c/2-2 = (77/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable254.value]
    have hcontinuation : (generalMeanRows 871).q*(generalMeanRows 871).cutoff/2-2 = (382/185:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable277.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 871).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 871

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 871).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 871).criticalRate j.val*(generalMeanRows 871).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 871).c*(generalMeanRows 871).criticalPoint j.val)).2-
      (generalMeanRows 871).J/2-(generalMeanRows 871).error (generalMeanGrid j.val)+
      (generalMeanRows 871).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 871).c)).2-
      (generalMeanRows 871).J/2-(generalMeanRows 871).error 4 := by
  have he : (generalMeanRows 871).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 871) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 871)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0871

/-! Kernel-checked entropy margins for general spectral rectangle 872. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0872
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5066782517) (.branch 2 (.leaf 4897769761) (.leaf 4736143750))) (.branch 5 (.branch 4 (.leaf 4581489650) (.leaf 4433421765)) (.branch 6 (.leaf 4291580988) (.leaf 4155632531)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4025263895) (.leaf 3900183046)) (.branch 10 (.leaf 3780116780) (.leaf 3664809240))) (.branch 13 (.branch 12 (.leaf 3554020579) (.leaf 3447525753)) (.branch 14 (.leaf 3345113415) (.leaf 3246584916))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3151753390) (.branch 17 (.leaf 3060442920) (.leaf 2972487776))) (.branch 20 (.branch 19 (.leaf 2887731710) (.leaf 2806027317)) (.branch 21 (.leaf 2727235440) (.leaf 2651224627)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2577870631) (.leaf 2507055940)) (.branch 25 (.leaf 2438669354) (.leaf 2372605585))) (.branch 28 (.branch 27 (.leaf 2308764887) (.leaf 2247052721)) (.branch 29 (.leaf 2187379431) (.leaf 2129659952)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2073813539) (.branch 32 (.leaf 2019763504) (.leaf 1967436988))) (.branch 35 (.branch 34 (.leaf 1916764728) (.leaf 1867680861)) (.branch 36 (.leaf 1820122720) (.leaf 1774030659)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1729347884) (.leaf 1686020291)) (.branch 40 (.leaf 1643996318) (.leaf 1603226810))) (.branch 43 (.branch 42 (.leaf 1563664881) (.leaf 1525265800)) (.branch 44 (.leaf 1487986868) (.leaf 1451787314))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1416628195) (.branch 47 (.leaf 1382472294) (.leaf 1349284038))) (.branch 50 (.branch 49 (.leaf 1317029407) (.leaf 1285675858)) (.branch 51 (.leaf 1255192246) (.leaf 1225548759)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1196716846) (.leaf 1168669156)) (.branch 55 (.leaf 1141379478) (.leaf 1114822686))) (.branch 58 (.branch 57 (.leaf 1088974685) (.leaf 1063812361)) (.branch 59 (.leaf 1039313534) (.leaf 1015456911))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 992222049) (.branch 62 (.leaf 969589309) (.leaf 947539821))) (.branch 65 (.branch 64 (.leaf 926055449) (.leaf 905118753)) (.branch 66 (.leaf 884712963) (.leaf 864821943)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 845430162) (.leaf 826522674)) (.branch 70 (.leaf 808085080) (.leaf 790103516))) (.branch 73 (.branch 72 (.leaf 772564619) (.leaf 755455510)) (.branch 74 (.leaf 738763775) (.leaf 722477438))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 706584948) (.branch 77 (.leaf 691075158) (.leaf 675937310))) (.branch 80 (.branch 79 (.leaf 661161015) (.leaf 646736242)) (.branch 81 (.leaf 632653298) (.leaf 618902819)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 605475752) (.leaf 592363347)) (.branch 85 (.leaf 579557140) (.leaf 567048945))) (.branch 88 (.branch 87 (.leaf 554830841) (.leaf 542895162)) (.branch 89 (.leaf 531234487) (.leaf 519841630)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 508709632) (.branch 92 (.leaf 497831751) (.leaf 487201454))) (.branch 95 (.branch 94 (.leaf 476812409) (.leaf 466658479)) (.branch 96 (.leaf 456733711) (.leaf 447032334)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 437548748) (.leaf 428277519)) (.branch 100 (.leaf 419213376) (.leaf 410351199))) (.branch 103 (.branch 102 (.leaf 401686020) (.leaf 393213014)) (.branch 104 (.leaf 384927492) (.leaf 376824904))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 368900823) (.leaf 361150952)) (.branch 108 (.leaf 353571112) (.leaf 346157238))) (.branch 111 (.branch 110 (.leaf 338905382) (.leaf 331811702)) (.branch 112 (.leaf 324872460) (.leaf 318084021)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 311442848) (.leaf 304945498)) (.branch 116 (.leaf 298588621) (.leaf 292368956))) (.branch 119 (.branch 118 (.leaf 286283325) (.leaf 280328638)) (.branch 120 (.leaf 274501883) (.leaf 268800126)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 872).prefactor = (4642889775161523/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 872).cutoff/(generalMeanRows 872).c)).2 =
    (92299003881469/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 872).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 872).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 872).q*(generalMeanRows 872).cutoff/2-2 = (382/185:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable277.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 872).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 872

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 872).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 872).criticalRate j.val*(generalMeanRows 872).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 872).c*(generalMeanRows 872).criticalPoint j.val)).2-
      (generalMeanRows 872).J/2-(generalMeanRows 872).error (generalMeanGrid j.val)+
      (generalMeanRows 872).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 872).c)).2-
      (generalMeanRows 872).J/2-(generalMeanRows 872).error 4 := by
  have he : (generalMeanRows 872).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 872) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 872)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0872

/-! Kernel-checked entropy margins for general spectral rectangle 873. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0873
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5027488959) (.branch 2 (.leaf 4857638236) (.leaf 4695215284))) (.branch 5 (.branch 4 (.leaf 4539804905) (.leaf 4391020964)) (.branch 6 (.leaf 4248503855) (.leaf 4111918231)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3980950983) (.leaf 3855309426)) (.branch 10 (.leaf 3734719658) (.leaf 3618925092))) (.branch 13 (.branch 12 (.leaf 3507685124) (.leaf 3400773921)) (.branch 14 (.leaf 3297979329) (.leaf 3199101874))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3103953849) (.branch 17 (.leaf 3012358488) (.leaf 2924149200))) (.branch 20 (.branch 19 (.leaf 2839168873) (.leaf 2757269234)) (.branch 21 (.leaf 2678310258) (.leaf 2602159628)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2528692233) (.leaf 2457789704)) (.branch 25 (.leaf 2389339989) (.leaf 2323236958))) (.branch 28 (.branch 27 (.leaf 2259380032) (.leaf 2197673847)) (.branch 29 (.leaf 2138027937) (.leaf 2080356438)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2024577818) (.branch 32 (.leaf 1970614618) (.leaf 1918393220))) (.branch 35 (.branch 34 (.leaf 1867843621) (.leaf 1818899225)) (.branch 36 (.leaf 1771496658) (.leaf 1725575576)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1681078503) (.leaf 1637950674)) (.branch 40 (.leaf 1596139878) (.leaf 1555596328))) (.branch 43 (.branch 42 (.leaf 1516272525) (.leaf 1478123139)) (.branch 44 (.leaf 1441104888) (.leaf 1405176437))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1370298291) (.branch 47 (.leaf 1336432702) (.leaf 1303543577))) (.branch 50 (.branch 49 (.leaf 1271596394) (.leaf 1240558122)) (.branch 51 (.leaf 1210397147) (.leaf 1181083199)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1152587284) (.leaf 1124881625)) (.branch 55 (.leaf 1097939596) (.leaf 1071735673))) (.branch 58 (.branch 57 (.leaf 1046245373) (.leaf 1021445212)) (.branch 59 (.leaf 997312648) (.leaf 973826043))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 950964620) (.branch 62 (.leaf 928708416) (.leaf 907038253))) (.branch 65 (.branch 64 (.leaf 885935695) (.leaf 865383016)) (.branch 66 (.leaf 845363168) (.leaf 825859750)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 806856978) (.leaf 788339658)) (.branch 70 (.leaf 770293158) (.leaf 752703387))) (.branch 73 (.branch 72 (.leaf 735556766) (.leaf 718840210)) (.branch 74 (.leaf 702541105) (.leaf 686647286))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 671147020) (.branch 77 (.leaf 656028988) (.leaf 641282263))) (.branch 80 (.branch 79 (.leaf 626896300) (.leaf 612860916)) (.branch 81 (.leaf 599166274) (.leaf 585802872)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 572761529) (.leaf 560033368)) (.branch 85 (.leaf 547609808) (.leaf 535482551))) (.branch 88 (.branch 87 (.leaf 523643569) (.leaf 512085096)) (.branch 89 (.leaf 500799615) (.leaf 489779850)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 479018757) (.branch 92 (.leaf 468509512) (.leaf 458245509))) (.branch 95 (.branch 94 (.leaf 448220343) (.leaf 438427810)) (.branch 96 (.leaf 428861896) (.leaf 419516769)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 410386775) (.leaf 401466430)) (.branch 100 (.leaf 392750413) (.leaf 384233562))) (.branch 103 (.branch 102 (.leaf 375910868) (.leaf 367777467)) (.branch 104 (.leaf 359828638) (.leaf 352059797))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 344466491) (.leaf 337044394)) (.branch 108 (.leaf 329789304) (.leaf 322697138))) (.branch 111 (.branch 110 (.leaf 315763927) (.leaf 308985812)) (.branch 112 (.leaf 302359044) (.leaf 295879975)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 289545057) (.leaf 283350840)) (.branch 116 (.leaf 277293968) (.leaf 271371176))) (.branch 119 (.branch 118 (.leaf 265579283) (.leaf 259915199)) (.branch 120 (.leaf 254375911) (.leaf 248958489)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 873).prefactor = (1163286714841199/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 873).cutoff/(generalMeanRows 873).c)).2 =
    (89178234645377/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 873).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 873).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 873).q*(generalMeanRows 873).c/2-2 = (83/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable255.value]
    have hcontinuation : (generalMeanRows 873).q*(generalMeanRows 873).cutoff/2-2 = (190/93:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable276.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 873).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 873

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 873).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 873).criticalRate j.val*(generalMeanRows 873).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 873).c*(generalMeanRows 873).criticalPoint j.val)).2-
      (generalMeanRows 873).J/2-(generalMeanRows 873).error (generalMeanGrid j.val)+
      (generalMeanRows 873).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 873).c)).2-
      (generalMeanRows 873).J/2-(generalMeanRows 873).error 4 := by
  have he : (generalMeanRows 873).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 873) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 873)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0873

/-! Kernel-checked entropy margins for general spectral rectangle 874. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0874
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4983796714) (.branch 2 (.leaf 4813212466) (.leaf 4650118577))) (.branch 5 (.branch 4 (.leaf 4494096536) (.leaf 4344757098)) (.branch 6 (.leaf 4201737733) (.leaf 4064700342)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3933329223) (.leaf 3807329242)) (.branch 10 (.leaf 3686424185) (.leaf 3570355280))) (.branch 13 (.branch 12 (.leaf 3458879851) (.leaf 3351770104)) (.branch 14 (.leaf 3248812027) (.leaf 3149804379))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3054557778) (.branch 17 (.leaf 2962893863) (.leaf 2874644528))) (.branch 20 (.branch 19 (.leaf 2789651218) (.leaf 2707764288)) (.branch 21 (.leaf 2628842403) (.leaf 2552751999)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2479366775) (.leaf 2408567227)) (.branch 25 (.leaf 2340240219) (.leaf 2274278585))) (.branch 28 (.branch 27 (.leaf 2210580759) (.leaf 2149050433)) (.branch 29 (.leaf 2089596236) (.leaf 2032131442)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1976573693) (.branch 32 (.leaf 1922844740) (.leaf 1870870209))) (.branch 35 (.branch 34 (.leaf 1820579373) (.leaf 1771904947)) (.branch 36 (.leaf 1724782890) (.leaf 1679152225)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1634954870) (.leaf 1592135475)) (.branch 40 (.leaf 1550641274) (.leaf 1510421945))) (.branch 43 (.branch 42 (.leaf 1471429479) (.leaf 1433618054)) (.branch 44 (.leaf 1396943920) (.leaf 1361365293))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1326842247) (.branch 47 (.leaf 1293336621) (.leaf 1260811927))) (.branch 50 (.branch 49 (.leaf 1229233267) (.leaf 1198567246)) (.branch 51 (.leaf 1168781902) (.leaf 1139846634)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1111732131) (.leaf 1084410309)) (.branch 55 (.leaf 1057854253) (.leaf 1032038159))) (.branch 58 (.branch 57 (.leaf 1006937279) (.leaf 982527871)) (.branch 59 (.leaf 958787151) (.leaf 935693249))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 913225161) (.branch 62 (.leaf 891362715) (.leaf 870086528))) (.branch 65 (.branch 64 (.leaf 849377970) (.leaf 829219129)) (.branch 66 (.leaf 809592780) (.leaf 790482355)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 771871906) (.leaf 753746088)) (.branch 70 (.leaf 736090122) (.leaf 718889778))) (.branch 73 (.branch 72 (.leaf 702131346) (.leaf 685801615)) (.branch 74 (.leaf 669887849) (.leaf 654377772))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 639259543) (.branch 77 (.leaf 624521739) (.leaf 610153339))) (.branch 80 (.branch 79 (.leaf 596143705) (.leaf 582482567)) (.branch 81 (.leaf 569160007) (.leaf 556166446)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 543492629) (.leaf 531129611)) (.branch 85 (.leaf 519068748) (.leaf 507301679))) (.branch 88 (.branch 87 (.leaf 495820322) (.leaf 484616856)) (.branch 89 (.leaf 473683716) (.leaf 463013579)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 452599358) (.branch 92 (.leaf 442434190) (.leaf 432511432))) (.branch 95 (.branch 94 (.leaf 422824646) (.leaf 413367595)) (.branch 96 (.leaf 404134238) (.leaf 395118718)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 386315356) (.leaf 377718648)) (.branch 100 (.leaf 369323254) (.leaf 361123996))) (.branch 103 (.branch 102 (.leaf 353115850) (.leaf 345293939)) (.branch 104 (.leaf 337653533) (.leaf 330190038))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 322898994) (.leaf 315776072)) (.branch 108 (.leaf 308817064) (.leaf 302017886))) (.branch 111 (.branch 110 (.leaf 295374568) (.leaf 288883253)) (.branch 112 (.leaf 282540193) (.leaf 276341743)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 270284361) (.leaf 264364604)) (.branch 116 (.leaf 258579121) (.leaf 252924656))) (.branch 119 (.branch 118 (.leaf 247398038) (.leaf 241996185)) (.branch 120 (.leaf 236716097) (.leaf 231554855)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 874).prefactor = (4686616926127301/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 874).cutoff/(generalMeanRows 874).c)).2 =
    (174835327978047/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 874).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 874).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 874).q*(generalMeanRows 874).c/2-2 = (17/20:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable055.value]
    have hcontinuation : (generalMeanRows 874).q*(generalMeanRows 874).cutoff/2-2 = (190/93:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable276.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 874).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 874

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 874).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 874).criticalRate j.val*(generalMeanRows 874).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 874).c*(generalMeanRows 874).criticalPoint j.val)).2-
      (generalMeanRows 874).J/2-(generalMeanRows 874).error (generalMeanGrid j.val)+
      (generalMeanRows 874).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 874).c)).2-
      (generalMeanRows 874).J/2-(generalMeanRows 874).error 4 := by
  have he : (generalMeanRows 874).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 874) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 874)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0874

/-! Kernel-checked entropy margins for general spectral rectangle 875. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0875
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5237212901) (.branch 2 (.leaf 5070003132) (.leaf 4909978113))) (.branch 5 (.branch 4 (.leaf 4756735389) (.leaf 4609900802)) (.branch 6 (.leaf 4469126007) (.leaf 4334086272)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4204478499) (.leaf 4080019455)) (.branch 10 (.leaf 3960444180) (.leaf 3845504549))) (.branch 13 (.branch 12 (.leaf 3734967971) (.leaf 3628616218)) (.branch 14 (.leaf 3526244349) (.leaf 3427659744))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3332681210) (.branch 17 (.leaf 3241138176) (.leaf 3152869950))) (.branch 20 (.branch 19 (.leaf 3067725036) (.leaf 2985560514)) (.branch 21 (.leaf 2906241464) (.leaf 2829640435)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2755636963) (.leaf 2684117114)) (.branch 25 (.leaf 2614973073) (.leaf 2548102757))) (.branch 28 (.branch 27 (.leaf 2483409458) (.leaf 2420801509)) (.branch 29 (.leaf 2360191983) (.leaf 2301498400)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2244642466) (.branch 32 (.leaf 2189549822) (.leaf 2136149815))) (.branch 35 (.branch 34 (.leaf 2084375283) (.leaf 2034162351)) (.branch 36 (.leaf 1985450247) (.leaf 1938181125)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1892299900) (.leaf 1847754092)) (.branch 40 (.leaf 1804493687) (.leaf 1762471000))) (.branch 43 (.branch 42 (.leaf 1721640545) (.leaf 1681958922)) (.branch 44 (.leaf 1643384698) (.leaf 1605878311))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1569401963) (.branch 47 (.leaf 1533919533) (.leaf 1499396486))) (.branch 50 (.branch 49 (.leaf 1465799795) (.leaf 1433097858)) (.branch 51 (.leaf 1401260433) (.leaf 1370258559)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1340064503) (.leaf 1310651688)) (.branch 55 (.leaf 1281994643) (.leaf 1254068945))) (.branch 58 (.branch 57 (.leaf 1226851169) (.leaf 1200318838)) (.branch 59 (.leaf 1174450377) (.leaf 1149225074))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1124623033) (.branch 62 (.leaf 1100625137) (.leaf 1077213015))) (.branch 65 (.branch 64 (.leaf 1054369001) (.leaf 1032076107)) (.branch 66 (.leaf 1010317986) (.leaf 989078909)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 968343730) (.leaf 948097867)) (.branch 70 (.leaf 928327269) (.leaf 909018398))) (.branch 73 (.branch 72 (.leaf 890158202) (.leaf 871734099)) (.branch 74 (.leaf 853733950) (.leaf 836146044))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 818959079) (.branch 77 (.leaf 802162143) (.leaf 785744698))) (.branch 80 (.branch 79 (.leaf 769696564) (.leaf 754007907)) (.branch 81 (.leaf 738669217) (.leaf 723671304)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 709005277) (.leaf 694662538)) (.branch 85 (.leaf 680634764) (.leaf 666913900))) (.branch 88 (.branch 87 (.leaf 653492149) (.leaf 640361959)) (.branch 89 (.leaf 627516013) (.leaf 614947224)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 602648721) (.branch 92 (.leaf 590613843) (.leaf 578836133))) (.branch 95 (.branch 94 (.leaf 567309327) (.leaf 556027347)) (.branch 96 (.leaf 544984295) (.leaf 534174449)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 523592251) (.leaf 513232304)) (.branch 100 (.leaf 503089368) (.leaf 493158349))) (.branch 103 (.branch 102 (.leaf 483434301) (.leaf 473912414)) (.branch 104 (.leaf 464588013) (.leaf 455456551))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 446513610) (.leaf 437754887)) (.branch 108 (.leaf 429176200) (.leaf 420773477))) (.branch 111 (.branch 110 (.leaf 412542756) (.leaf 404480180)) (.branch 112 (.leaf 396581992) (.leaf 388844536)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 381264250) (.leaf 373837662)) (.branch 116 (.leaf 366561394) (.leaf 359432149))) (.branch 119 (.branch 118 (.leaf 352446717) (.leaf 345601967)) (.branch 120 (.leaf 338894849) (.leaf 332322386)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 875).prefactor = (2275929568388031/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 875).cutoff/(generalMeanRows 875).c)).2 =
    (192785286635461/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 875).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 875).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 875).q*(generalMeanRows 875).c/2-2 = (6041/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable278.value]
    have hcontinuation : (generalMeanRows 875).q*(generalMeanRows 875).cutoff/2-2 = (80/39:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable279.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 875).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 875

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 875).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 875).criticalRate j.val*(generalMeanRows 875).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 875).c*(generalMeanRows 875).criticalPoint j.val)).2-
      (generalMeanRows 875).J/2-(generalMeanRows 875).error (generalMeanGrid j.val)+
      (generalMeanRows 875).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 875).c)).2-
      (generalMeanRows 875).J/2-(generalMeanRows 875).error 4 := by
  have he : (generalMeanRows 875).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 875) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 875)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0875

/-! Kernel-checked entropy margins for general spectral rectangle 876. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0876
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5063032718) (.branch 2 (.leaf 4894591015) (.leaf 4733469564))) (.branch 5 (.branch 4 (.leaf 4579259295) (.leaf 4431579807)) (.branch 6 (.leaf 4290076862) (.leaf 4154420151)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4024301295) (.leaf 3899432054)) (.branch 10 (.leaf 3779542711) (.leaf 3664380623))) (.branch 13 (.branch 12 (.leaf 3553708900) (.leaf 3447305219)) (.branch 14 (.leaf 3344960738) (.leaf 3246479111))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3151675595) (.branch 17 (.leaf 3060376222) (.leaf 2972417053))) (.branch 20 (.branch 19 (.leaf 2887643491) (.leaf 2805909642)) (.branch 21 (.leaf 2727077740) (.leaf 2651017609)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2577606170) (.leaf 2506726984)) (.branch 25 (.leaf 2438269831) (.leaf 2372130321))) (.branch 28 (.branch 27 (.leaf 2308209530) (.leaf 2246413664)) (.branch 29 (.leaf 2186653752) (.leaf 2128845351)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2072908280) (.branch 32 (.leaf 2018766365) (.leaf 1966347209))) (.branch 35 (.branch 34 (.leaf 1915581974) (.leaf 1866405172)) (.branch 36 (.leaf 1818754479) (.leaf 1772570556)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1727796883) (.leaf 1684379598)) (.branch 40 (.leaf 1642267360) (.leaf 1601411202))) (.branch 43 (.branch 42 (.leaf 1561764410) (.leaf 1523282397)) (.branch 44 (.leaf 1485922594) (.leaf 1449644340))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1414408784) (.branch 47 (.leaf 1380178788) (.leaf 1346918843))) (.branch 50 (.branch 49 (.leaf 1314594981) (.leaf 1283174698)) (.branch 51 (.leaf 1252626882) (.leaf 1222921738)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1194030727) (.leaf 1165926502)) (.branch 55 (.leaf 1138582849) (.leaf 1111974632))) (.branch 58 (.branch 57 (.leaf 1086077739) (.leaf 1060869036)) (.branch 59 (.leaf 1036326317) (.leaf 1012428260))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 989154388) (.branch 62 (.leaf 966485024) (.leaf 944401261))) (.branch 65 (.branch 64 (.leaf 922884918) (.leaf 901918514)) (.branch 66 (.leaf 881485230) (.leaf 861568883)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 842153894) (.leaf 823225266)) (.branch 70 (.leaf 804768550) (.leaf 786769829))) (.branch 73 (.branch 72 (.leaf 769215688) (.leaf 752093198)) (.branch 74 (.leaf 735389889) (.leaf 719093735))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 703193131) (.branch 77 (.leaf 687676878) (.leaf 672534167))) (.branch 80 (.branch 79 (.leaf 657754556) (.leaf 643327963)) (.branch 81 (.leaf 629244646) (.leaf 615495189)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 602070491) (.leaf 588961753)) (.branch 85 (.leaf 576160464) (.leaf 563658390))) (.branch 88 (.branch 87 (.leaf 551447565) (.leaf 539520276)) (.branch 89 (.leaf 527869059) (.leaf 516486684)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 505366150) (.branch 92 (.leaf 494500673) (.leaf 483883680))) (.branch 95 (.branch 94 (.leaf 473508798) (.leaf 463369853)) (.branch 96 (.leaf 453460853) (.leaf 443775990)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 434309629) (.leaf 425056302)) (.branch 100 (.leaf 416010702) (.leaf 407167677))) (.branch 103 (.branch 102 (.leaf 398522227) (.leaf 390069495)) (.branch 104 (.leaf 381804764) (.leaf 373723452))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 365821106) (.leaf 358093399)) (.branch 108 (.leaf 350536126) (.leaf 343145198))) (.branch 111 (.branch 110 (.leaf 335916639) (.leaf 328846585)) (.branch 112 (.leaf 321931273) (.leaf 315167047)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 308550346) (.leaf 302077708)) (.branch 116 (.leaf 295745761) (.leaf 289551224))) (.branch 119 (.branch 118 (.leaf 283490902) (.leaf 277561685)) (.branch 120 (.leaf 271760543) (.leaf 266084526)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 876).prefactor = (288580346407003/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 876).cutoff/(generalMeanRows 876).c)).2 =
    (182146587411819/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 876).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 876).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 876).q*(generalMeanRows 876).c/2-2 = (1303/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable271.value]
    have hcontinuation : (generalMeanRows 876).q*(generalMeanRows 876).cutoff/2-2 = (80/39:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable279.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 876).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 876

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 876).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 876).criticalRate j.val*(generalMeanRows 876).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 876).c*(generalMeanRows 876).criticalPoint j.val)).2-
      (generalMeanRows 876).J/2-(generalMeanRows 876).error (generalMeanGrid j.val)+
      (generalMeanRows 876).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 876).c)).2-
      (generalMeanRows 876).J/2-(generalMeanRows 876).error 4 := by
  have he : (generalMeanRows 876).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 876) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 876)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0876

/-! Kernel-checked entropy margins for general spectral rectangle 877. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0877
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5021381644) (.branch 2 (.leaf 4851629298) (.leaf 4689325581))) (.branch 5 (.branch 4 (.leaf 4534052433) (.leaf 4385421122)) (.branch 6 (.leaf 4243069688) (.leaf 4106660659)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3975879003) (.leaf 3850430298)) (.branch 10 (.leaf 3730039080) (.leaf 3614447356))) (.branch 13 (.branch 12 (.leaf 3503413257) (.leaf 3396709820)) (.branch 14 (.leaf 3294123880) (.leaf 3195455060))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3100514853) (.branch 17 (.leaf 3009125782) (.leaf 2921120630))) (.branch 20 (.branch 19 (.leaf 2836341735) (.leaf 2754640345)) (.branch 21 (.leaf 2675876019) (.leaf 2599916079)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2526635109) (.leaf 2455914480)) (.branch 25 (.leaf 2387641926) (.leaf 2321711139))) (.branch 28 (.branch 27 (.leaf 2258021400) (.leaf 2196477238)) (.branch 29 (.leaf 2136988106) (.leaf 2079468086)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2023835617) (.branch 32 (.leaf 1970013230) (.leaf 1917927317))) (.branch 35 (.branch 34 (.leaf 1867507899) (.leaf 1818688426)) (.branch 36 (.leaf 1771405573) (.leaf 1725599064)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1681211500) (.leaf 1638188198)) (.branch 40 (.leaf 1596477042) (.leaf 1556028342))) (.branch 43 (.branch 42 (.leaf 1516794704) (.leaf 1478730905)) (.branch 44 (.leaf 1441793778) (.leaf 1405942102))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1371136502) (.branch 47 (.leaf 1337339348) (.leaf 1304514668))) (.branch 50 (.branch 49 (.leaf 1272628063) (.leaf 1241646623)) (.branch 51 (.leaf 1211538857) (.leaf 1182274614)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1153825022) (.leaf 1126162423)) (.branch 55 (.leaf 1099260310) (.leaf 1073093274))) (.branch 58 (.branch 57 (.leaf 1047636948) (.leaf 1022867960)) (.branch 59 (.leaf 998763878) (.leaf 975303175))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 952465177) (.branch 62 (.leaf 930230027) (.leaf 908578647))) (.branch 65 (.branch 64 (.leaf 887492701) (.leaf 866954558)) (.branch 66 (.leaf 846947265) (.leaf 827454511)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 808460601) (.leaf 789950426)) (.branch 70 (.leaf 771909439) (.leaf 754323627))) (.branch 73 (.branch 72 (.leaf 737179492) (.leaf 720464022)) (.branch 74 (.leaf 704164677) (.leaf 688269362))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 672766413) (.branch 77 (.leaf 657644574) (.leaf 642892985))) (.branch 80 (.branch 79 (.leaf 628501159) (.leaf 614458972)) (.branch 81 (.leaf 600756644) (.leaf 587384728)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 574334092) (.leaf 561595912)) (.branch 85 (.leaf 549161654) (.leaf 537023066))) (.branch 88 (.branch 87 (.leaf 525172164) (.leaf 513601224)) (.branch 89 (.leaf 502302769) (.leaf 491269564)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 480494598) (.branch 92 (.leaf 469971087) (.leaf 459692455))) (.branch 95 (.branch 94 (.leaf 449652332) (.leaf 439844542)) (.branch 96 (.leaf 430263102) (.leaf 420902208)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 411756231) (.leaf 402819715)) (.branch 100 (.leaf 394087361) (.leaf 385554030))) (.branch 103 (.branch 102 (.leaf 377214735) (.leaf 369064633)) (.branch 104 (.leaf 361099023) (.leaf 353313337))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 345703141) (.leaf 338264126)) (.branch 108 (.leaf 330992106) (.leaf 323883012))) (.branch 111 (.branch 110 (.leaf 316932888) (.leaf 310137890)) (.branch 112 (.leaf 303494279) (.leaf 296998420)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 290646777) (.leaf 284435909)) (.branch 116 (.leaf 278362469) (.leaf 272423201))) (.branch 119 (.branch 118 (.leaf 266614934) (.leaf 260934583)) (.branch 120 (.leaf 255379145) (.leaf 249945695)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 877).prefactor = (2337854657196873/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 877).cutoff/(generalMeanRows 877).c)).2 =
    (707233959407/1953125000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 877).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 877).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 877).q*(generalMeanRows 877).c/2-2 = (83/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable255.value]
    have hcontinuation : (generalMeanRows 877).q*(generalMeanRows 877).cutoff/2-2 = (382/185:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable277.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 877).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 877

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 877).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 877).criticalRate j.val*(generalMeanRows 877).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 877).c*(generalMeanRows 877).criticalPoint j.val)).2-
      (generalMeanRows 877).J/2-(generalMeanRows 877).error (generalMeanGrid j.val)+
      (generalMeanRows 877).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 877).c)).2-
      (generalMeanRows 877).J/2-(generalMeanRows 877).error 4 := by
  have he : (generalMeanRows 877).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 877) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 877)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0877

/-! Kernel-checked entropy margins for general spectral rectangle 878. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0878
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4976770160) (.branch 2 (.leaf 4806305082) (.leaf 4643350506))) (.branch 5 (.branch 4 (.leaf 4487485094) (.leaf 4338317038)) (.branch 6 (.leaf 4195481488) (.leaf 4058638247)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3927469718) (.leaf 3801679058)) (.branch 10 (.leaf 3680988515) (.leaf 3565137933))) (.branch 13 (.branch 12 (.leaf 3453883394) (.leaf 3346995994)) (.branch 14 (.leaf 3244260728) (.leaf 3145475471))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3050450059) (.branch 17 (.leaf 2959005435) (.leaf 2870972883))) (.branch 20 (.branch 19 (.leaf 2786193314) (.leaf 2704516615)) (.branch 21 (.leaf 2625801049) (.leaf 2549912704)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2476724983) (.leaf 2406118137)) (.branch 25 (.leaf 2337978825) (.leaf 2272199713))) (.branch 28 (.branch 27 (.leaf 2208679105) (.leaf 2147320593)) (.branch 29 (.leaf 2088032735) (.leaf 2030728760)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1975326287) (.branch 32 (.leaf 1921747067) (.leaf 1869916740))) (.branch 35 (.branch 34 (.leaf 1819764614) (.leaf 1771223449)) (.branch 36 (.leaf 1724229267) (.leaf 1678721161)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1634641132) (.leaf 1591933918)) (.branch 40 (.leaf 1550546852) (.leaf 1510429714))) (.branch 43 (.branch 42 (.leaf 1471534605) (.leaf 1433815816)) (.branch 44 (.leaf 1397229715) (.leaf 1361734636))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1327290775) (.branch 47 (.leaf 1293860096) (.leaf 1261406235))) (.branch 50 (.branch 49 (.leaf 1229894418) (.leaf 1199291376)) (.branch 51 (.leaf 1169565273) (.leaf 1140685631)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1112623263) (.leaf 1085350207)) (.branch 55 (.leaf 1058839669) (.leaf 1033065963))) (.branch 58 (.branch 57 (.leaf 1008004459) (.leaf 983631531)) (.branch 59 (.leaf 959924507) (.leaf 936861627))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 914421997) (.branch 62 (.leaf 892585550) (.leaf 871333006))) (.branch 65 (.branch 64 (.leaf 850645835) (.leaf 830506226)) (.branch 66 (.leaf 810897047) (.leaf 791801822)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 773204696) (.leaf 755090409)) (.branch 70 (.leaf 737444269) (.leaf 720252126))) (.branch 73 (.branch 72 (.leaf 703500350) (.leaf 687175806)) (.branch 74 (.leaf 671265835) (.leaf 655758231))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 640641222) (.branch 77 (.leaf 625903453) (.leaf 611533966))) (.branch 80 (.branch 79 (.leaf 597522186) (.leaf 583857901)) (.branch 81 (.leaf 570531253) (.leaf 557532718)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 544853092) (.leaf 532483483)) (.branch 85 (.leaf 520415294) (.leaf 508640214))) (.branch 88 (.branch 87 (.leaf 497150202) (.leaf 485937484)) (.branch 89 (.leaf 474994533) (.leaf 464314069)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 453889040) (.branch 92 (.leaf 443712621) (.leaf 433778202))) (.branch 95 (.branch 94 (.leaf 424079379) (.leaf 414609948)) (.branch 96 (.leaf 405363895) (.leaf 396335392)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 387518790) (.leaf 378908609)) (.branch 100 (.leaf 370499534) (.leaf 362286411))) (.branch 103 (.branch 102 (.leaf 354264237) (.leaf 346428159)) (.branch 104 (.leaf 338773464) (.leaf 331295578))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 323990061) (.leaf 316852599)) (.branch 108 (.leaf 309879001) (.leaf 303065198))) (.branch 111 (.branch 110 (.leaf 296407236) (.leaf 289901269)) (.branch 112 (.leaf 283543564) (.leaf 277330487)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 271258509) (.leaf 265324196)) (.branch 116 (.leaf 259524207) (.leaf 253855296))) (.branch 119 (.branch 118 (.leaf 248314302) (.leaf 242898149)) (.branch 120 (.leaf 237603847) (.leaf 232428482)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 878).prefactor = (4708760847536567/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 878).cutoff/(generalMeanRows 878).c)).2 =
    (355061504590973/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 878).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 878).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 878).q*(generalMeanRows 878).c/2-2 = (17/20:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable055.value]
    have hcontinuation : (generalMeanRows 878).q*(generalMeanRows 878).cutoff/2-2 = (382/185:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable277.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 878).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 878

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 878).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 878).criticalRate j.val*(generalMeanRows 878).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 878).c*(generalMeanRows 878).criticalPoint j.val)).2-
      (generalMeanRows 878).J/2-(generalMeanRows 878).error (generalMeanGrid j.val)+
      (generalMeanRows 878).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 878).c)).2-
      (generalMeanRows 878).J/2-(generalMeanRows 878).error 4 := by
  have he : (generalMeanRows 878).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 878) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 878)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0878

/-! Kernel-checked entropy margins for general spectral rectangle 879. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0879
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4940867383) (.branch 2 (.leaf 4769575391) (.leaf 4605836322))) (.branch 5 (.branch 4 (.leaf 4449228307) (.leaf 4299358948)) (.branch 6 (.leaf 4155862752) (.leaf 4018398832)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3886648859) (.leaf 3760315218)) (.branch 10 (.leaf 3639119355) (.leaf 3522800284))) (.branch 13 (.branch 12 (.leaf 3411113235) (.leaf 3303828431)) (.branch 14 (.leaf 3200729977) (.leaf 3101614849))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3006291971) (.branch 17 (.leaf 2914581373) (.leaf 2826313418))) (.branch 20 (.branch 19 (.leaf 2741328097) (.leaf 2659474378)) (.branch 21 (.leaf 2580609609) (.leaf 2504598968)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2431314956) (.leaf 2360636926)) (.branch 25 (.leaf 2292450653) (.leaf 2226647932))) (.branch 28 (.branch 27 (.leaf 2163126203) (.leaf 2101788209)) (.branch 29 (.leaf 2042541676) (.leaf 1985299011)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1929977029) (.branch 32 (.leaf 1876496692) (.leaf 1824782868))) (.branch 35 (.branch 34 (.leaf 1774764110) (.leaf 1726372440)) (.branch 36 (.leaf 1679543156) (.leaf 1634214650)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1590328235) (.leaf 1547827981)) (.branch 40 (.leaf 1506660569) (.leaf 1466775147))) (.branch 43 (.branch 42 (.leaf 1428123198) (.leaf 1390658416)) (.branch 44 (.leaf 1354336587) (.leaf 1319115481))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1284954749) (.branch 47 (.leaf 1251815822) (.leaf 1219661823))) (.branch 50 (.branch 49 (.leaf 1188457482) (.leaf 1158169048)) (.branch 51 (.leaf 1128764220) (.leaf 1100212069)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1072482973) (.leaf 1045548552)) (.branch 55 (.leaf 1019381607) (.leaf 993956061))) (.branch 58 (.branch 57 (.leaf 969246907) (.leaf 945230155)) (.branch 59 (.leaf 921882785) (.leaf 899182700))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 877108682) (.branch 62 (.leaf 855640353) (.leaf 834758133))) (.branch 65 (.branch 64 (.leaf 814443206) (.leaf 794677483)) (.branch 66 (.leaf 775443569) (.leaf 756724733)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 738504877) (.leaf 720768508)) (.branch 70 (.leaf 703500709) (.leaf 686687118))) (.branch 73 (.branch 72 (.leaf 670313901) (.leaf 654367727)) (.branch 74 (.leaf 638835751) (.leaf 623705588))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 608965297) (.branch 77 (.leaf 594603361) (.leaf 580608669))) (.branch 80 (.branch 79 (.leaf 566970498) (.leaf 553678499)) (.branch 81 (.leaf 540722679) (.leaf 528093389)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 515781307) (.leaf 503777428)) (.branch 85 (.leaf 492073048) (.leaf 480659755))) (.branch 88 (.branch 87 (.leaf 469529414) (.leaf 458674159)) (.branch 89 (.leaf 448086380) (.leaf 437758717)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 427684045) (.branch 92 (.leaf 417855469) (.leaf 408266311))) (.branch 95 (.branch 94 (.leaf 398910108) (.leaf 389780599)) (.branch 96 (.leaf 380871718) (.leaf 372177588)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 363692513) (.leaf 355410973)) (.branch 100 (.leaf 347327615) (.leaf 339437250))) (.branch 103 (.branch 102 (.leaf 331734843) (.leaf 324215512)) (.branch 104 (.leaf 316874520) (.leaf 309707269))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 302709298) (.leaf 295876276)) (.branch 108 (.leaf 289203997) (.leaf 282688380))) (.branch 111 (.branch 110 (.leaf 276325457) (.leaf 270111378)) (.branch 112 (.leaf 264042400) (.leaf 258114887)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 252325305) (.leaf 246670221)) (.branch 116 (.leaf 241146295) (.leaf 235750283))) (.branch 119 (.branch 118 (.leaf 230479027) (.leaf 225329458)) (.branch 120 (.leaf 220298593) (.leaf 215383525)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 879).prefactor = (2360163871473133/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 879).cutoff/(generalMeanRows 879).c)).2 =
    (2741420963721/8000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 879).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 879).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 879).q*(generalMeanRows 879).c/2-2 = (87/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable246.value]
    have hcontinuation : (generalMeanRows 879).q*(generalMeanRows 879).cutoff/2-2 = (190/93:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable276.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 879).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 879

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 879).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 879).criticalRate j.val*(generalMeanRows 879).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 879).c*(generalMeanRows 879).criticalPoint j.val)).2-
      (generalMeanRows 879).J/2-(generalMeanRows 879).error (generalMeanGrid j.val)+
      (generalMeanRows 879).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 879).c)).2-
      (generalMeanRows 879).J/2-(generalMeanRows 879).error 4 := by
  have he : (generalMeanRows 879).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 879) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 879)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0879

/-! Kernel-checked entropy margins for general spectral rectangle 880. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0880
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5314873860) (.branch 2 (.leaf 5147534719) (.leaf 4987407574))) (.branch 5 (.branch 4 (.leaf 4834084676) (.leaf 4687187107)) (.branch 6 (.leaf 4546362258) (.leaf 4411281574)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4281638548) (.leaf 4157146907)) (.branch 10 (.leaf 4037538993) (.leaf 3922564291))) (.branch 13 (.branch 12 (.leaf 3811988108) (.leaf 3705590365)) (.branch 14 (.leaf 3603164511) (.leaf 3504516526))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3409464014) (.branch 17 (.leaf 3317835380) (.leaf 3229469064))) (.branch 20 (.branch 19 (.leaf 3144212853) (.leaf 3061923240)) (.branch 21 (.leaf 2982464838) (.leaf 2905709840)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2831537522) (.leaf 2759833778)) (.branch 25 (.leaf 2690490703) (.leaf 2623406192))) (.branch 28 (.branch 27 (.leaf 2558483580) (.leaf 2495631302)) (.branch 29 (.leaf 2434762581) (.leaf 2375795133)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2318650899) (.branch 32 (.leaf 2263255791) (.leaf 2209539458))) (.branch 35 (.branch 34 (.leaf 2157435063) (.leaf 2106879082)) (.branch 36 (.leaf 2057811112) (.leaf 2010173692)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1963912134) (.leaf 1918974370)) (.branch 40 (.leaf 1875310803) (.leaf 1832874172))) (.branch 43 (.branch 42 (.leaf 1791619422) (.leaf 1751503582)) (.branch 44 (.leaf 1712485654) (.leaf 1674526508))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1637588779) (.branch 47 (.leaf 1601636773) (.leaf 1566636383))) (.branch 50 (.branch 49 (.leaf 1532555001) (.leaf 1499361443)) (.branch 51 (.leaf 1467025876) (.leaf 1435519744)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1404815708) (.leaf 1374887583)) (.branch 55 (.leaf 1345710278) (.leaf 1317259744))) (.branch 58 (.branch 57 (.leaf 1289512919) (.leaf 1262447683)) (.branch 59 (.leaf 1236042809) (.leaf 1210277921))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1185133453) (.branch 62 (.leaf 1160590607) (.leaf 1136631322))) (.branch 65 (.branch 64 (.leaf 1113238235) (.leaf 1090394646)) (.branch 66 (.leaf 1068084495) (.leaf 1046292323)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1025003250) (.leaf 1004202948)) (.branch 70 (.leaf 983877613) (.leaf 964013944))) (.branch 73 (.branch 72 (.leaf 944599119) (.leaf 925620775)) (.branch 74 (.leaf 907066986) (.leaf 888926244))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 871187444) (.branch 77 (.leaf 853839860) (.leaf 836873135))) (.branch 80 (.branch 79 (.leaf 820277262) (.leaf 804042570)) (.branch 81 (.leaf 788159709) (.leaf 772619639)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 757413614) (.leaf 742533171)) (.branch 85 (.leaf 727970120) (.leaf 713716531))) (.branch 88 (.branch 87 (.leaf 699764724) (.leaf 686107258)) (.branch 89 (.leaf 672736926) (.leaf 659646740)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 646829924) (.branch 92 (.leaf 634279910) (.leaf 621990323))) (.branch 95 (.branch 94 (.leaf 609954981) (.leaf 598167881)) (.branch 96 (.leaf 586623197) (.leaf 575315272)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564238609) (.leaf 553387872)) (.branch 100 (.leaf 542757871) (.leaf 532343566))) (.branch 103 (.branch 102 (.leaf 522140053) (.leaf 512142567)) (.branch 104 (.leaf 502346472) (.leaf 492747257))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 483340533) (.leaf 474122032)) (.branch 108 (.leaf 465087593) (.leaf 456233171))) (.branch 111 (.branch 110 (.leaf 447554823) (.leaf 439048709)) (.branch 112 (.leaf 430711091) (.leaf 422538322)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 414526852) (.leaf 406673220)) (.branch 116 (.leaf 398974049) (.leaf 391426051))) (.branch 119 (.branch 118 (.leaf 384026015) (.leaf 376770813)) (.branch 120 (.leaf 369657390) (.leaf 362682767)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 880).prefactor = (4595672824760777/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 880).cutoff/(generalMeanRows 880).c)).2 =
    (403460138021697/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 880).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 880).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 880).q*(generalMeanRows 880).c/2-2 = (5883/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable280.value]
    have hcontinuation : (generalMeanRows 880).q*(generalMeanRows 880).cutoff/2-2 = (7598/3627:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable281.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 880).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 880

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 880).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 880).criticalRate j.val*(generalMeanRows 880).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 880).c*(generalMeanRows 880).criticalPoint j.val)).2-
      (generalMeanRows 880).J/2-(generalMeanRows 880).error (generalMeanGrid j.val)+
      (generalMeanRows 880).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 880).c)).2-
      (generalMeanRows 880).J/2-(generalMeanRows 880).error 4 := by
  have he : (generalMeanRows 880).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 880) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 880)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0880

/-! Kernel-checked entropy margins for general spectral rectangle 881. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0881
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5216041759) (.branch 2 (.leaf 5047057794) (.leaf 4885409039))) (.branch 5 (.branch 4 (.leaf 4730681625) (.leaf 4582490884)) (.branch 6 (.leaf 4440478795) (.leaf 4304311707)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4173678305) (.leaf 4048287772)) (.branch 10 (.leaf 3927868153) (.leaf 3812164866))) (.branch 13 (.branch 12 (.leaf 3700939358) (.leaf 3593967892)) (.branch 14 (.leaf 3491040441) (.leaf 3391959678))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3296540065) (.branch 17 (.leaf 3204607009) (.leaf 3115996097))) (.branch 20 (.branch 19 (.leaf 3030552395) (.leaf 2948129797)) (.branch 21 (.leaf 2868590435) (.leaf 2791804132)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2717647896) (.leaf 2646005454)) (.branch 25 (.leaf 2576766825) (.leaf 2509827917))) (.branch 28 (.branch 27 (.leaf 2445090161) (.leaf 2382460167)) (.branch 29 (.leaf 2321849409) (.leaf 2263173925)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2206354047) (.branch 32 (.leaf 2151314140) (.leaf 2097982370))) (.branch 35 (.branch 34 (.leaf 2046290477) (.leaf 1996173566)) (.branch 36 (.leaf 1947569921) (.leaf 1900420816)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1854670349) (.leaf 1810265283)) (.branch 40 (.leaf 1767154900) (.leaf 1725290857))) (.branch 43 (.branch 42 (.leaf 1684627060) (.leaf 1645119539)) (.branch 44 (.leaf 1606726335) (.leaf 1569407392))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1533124454) (.branch 47 (.leaf 1497840971) (.leaf 1463522011))) (.branch 50 (.branch 49 (.leaf 1430134173) (.leaf 1397645508)) (.branch 51 (.leaf 1366025447) (.leaf 1335244728)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1305275331) (.leaf 1276090413)) (.branch 55 (.leaf 1247664254) (.leaf 1219972196))) (.branch 58 (.branch 57 (.leaf 1192990594) (.leaf 1166696764)) (.branch 59 (.leaf 1141068939) (.leaf 1116086222))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1091728545) (.branch 62 (.leaf 1067976631) (.leaf 1044811952))) (.branch 65 (.branch 64 (.leaf 1022216700) (.leaf 1000173749)) (.branch 66 (.leaf 978666624) (.leaf 957679472)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 937197032) (.leaf 917204609)) (.branch 70 (.leaf 897688050) (.leaf 878633715))) (.branch 73 (.branch 72 (.leaf 860028459) (.leaf 841859607)) (.branch 74 (.leaf 824114936) (.leaf 806782653))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 789851375) (.branch 77 (.leaf 773310117) (.leaf 757148267))) (.branch 80 (.branch 79 (.leaf 741355578) (.leaf 725922148)) (.branch 81 (.leaf 710838407) (.leaf 696095100)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 681683281) (.leaf 667594293)) (.branch 85 (.leaf 653819761) (.leaf 640351580))) (.branch 88 (.branch 87 (.leaf 627181900) (.leaf 614303121)) (.branch 89 (.leaf 601707883) (.leaf 589389051)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 577339714) (.branch 92 (.leaf 565553168) (.leaf 554022917))) (.branch 95 (.branch 94 (.leaf 542742658) (.leaf 531706277)) (.branch 96 (.leaf 520907842) (.leaf 510341593)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 500001942) (.leaf 489883460)) (.branch 100 (.leaf 479980874) (.leaf 470289064))) (.branch 103 (.branch 102 (.leaf 460803054) (.leaf 451518006)) (.branch 104 (.leaf 442429221) (.leaf 433532126))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 424822277) (.leaf 416295351)) (.branch 108 (.leaf 407947142) (.leaf 399773557))) (.branch 111 (.branch 110 (.leaf 391770613) (.leaf 383934434)) (.branch 112 (.leaf 376261246) (.leaf 368747373)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 361389237) (.leaf 354183351)) (.branch 116 (.leaf 347126319) (.leaf 340214832))) (.branch 119 (.branch 118 (.leaf 333445665) (.leaf 326815675)) (.branch 120 (.leaf 320321797) (.leaf 313961046)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 881).prefactor = (291216428595997/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 881).cutoff/(generalMeanRows 881).c)).2 =
    (389122974875291/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 881).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 881).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 881).q*(generalMeanRows 881).c/2-2 = (6199/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable268.value]
    have hcontinuation : (generalMeanRows 881).q*(generalMeanRows 881).cutoff/2-2 = (7598/3627:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable281.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 881).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 881

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 881).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 881).criticalRate j.val*(generalMeanRows 881).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 881).c*(generalMeanRows 881).criticalPoint j.val)).2-
      (generalMeanRows 881).J/2-(generalMeanRows 881).error (generalMeanGrid j.val)+
      (generalMeanRows 881).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 881).c)).2-
      (generalMeanRows 881).J/2-(generalMeanRows 881).error 4 := by
  have he : (generalMeanRows 881).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 881) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 881)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0881

/-! Kernel-checked entropy margins for general spectral rectangle 882. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0882
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4897921680) (.branch 2 (.leaf 4728512760) (.leaf 4566557532))) (.branch 5 (.branch 4 (.leaf 4411640008) (.leaf 4263373269)) (.branch 6 (.leaf 4121396924) (.leaf 3985374847)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3854993159) (.leaf 3729958406)) (.branch 10 (.leaf 3609995930) (.leaf 3494848393))) (.branch 13 (.branch 12 (.leaf 3384274447) (.leaf 3278047531)) (.branch 14 (.leaf 3175954765) (.leaf 3077795964))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2983382719) (.branch 17 (.leaf 2892537570) (.leaf 2805093246))) (.branch 20 (.branch 19 (.leaf 2720891965) (.leaf 2639784795)) (.branch 21 (.leaf 2561631065) (.leaf 2486297821)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2413659327) (.leaf 2343596602)) (.branch 25 (.leaf 2275996994) (.leaf 2210753784))) (.branch 28 (.branch 27 (.leaf 2147765815) (.leaf 2086937160)) (.branch 29 (.leaf 2028176799) (.leaf 1971398327)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1916519684) (.branch 32 (.leaf 1863462894) (.leaf 1812153833))) (.branch 35 (.branch 34 (.leaf 1762522005) (.leaf 1714500336)) (.branch 36 (.leaf 1668024979) (.leaf 1623035134)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1579472880) (.leaf 1537283017)) (.branch 40 (.leaf 1496412911) (.leaf 1456812365))) (.branch 43 (.branch 42 (.leaf 1418433479) (.leaf 1381230533)) (.branch 44 (.leaf 1345159870) (.leaf 1310179786))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1276250431) (.branch 47 (.leaf 1243333711) (.leaf 1211393199))) (.branch 50 (.branch 49 (.leaf 1180394049) (.leaf 1150302915)) (.branch 51 (.leaf 1121087879) (.leaf 1092718377)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1065165131) (.leaf 1038400088)) (.branch 55 (.leaf 1012396359) (.leaf 987128162))) (.branch 58 (.branch 57 (.leaf 962570769) (.leaf 938700457)) (.branch 59 (.leaf 915494455) (.leaf 892930906))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 870988819) (.branch 62 (.leaf 849648029) (.leaf 828889162))) (.branch 65 (.branch 64 (.leaf 808693595) (.leaf 789043422)) (.branch 66 (.leaf 769921423) (.leaf 751311032)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 733196308) (.leaf 715561908)) (.branch 70 (.leaf 698393055) (.leaf 681675523))) (.branch 73 (.branch 72 (.leaf 665395603) (.leaf 649540087)) (.branch 74 (.leaf 634096244) (.leaf 619051798))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 604394912) (.branch 77 (.leaf 590114167) (.leaf 576198545))) (.branch 80 (.branch 79 (.leaf 562637412) (.leaf 549420502)) (.branch 81 (.leaf 536537903) (.leaf 523980041)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 511737667) (.leaf 499801843)) (.branch 85 (.leaf 488163932) (.leaf 476815581))) (.branch 88 (.branch 87 (.leaf 465748715) (.leaf 454955524)) (.branch 89 (.leaf 444428452) (.leaf 434160186)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 424143651) (.branch 92 (.leaf 414371996) (.leaf 404838589))) (.branch 95 (.branch 94 (.leaf 395537005) (.leaf 386461023)) (.branch 96 (.leaf 377604614) (.leaf 368961937)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 360527329) (.leaf 352295302)) (.branch 100 (.leaf 344260534) (.leaf 336417864))) (.branch 103 (.branch 102 (.leaf 328762285) (.leaf 321288941)) (.branch 104 (.leaf 313993120) (.leaf 306870249))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 299915888) (.leaf 293125728)) (.branch 108 (.leaf 286495584) (.leaf 280021395))) (.branch 111 (.branch 110 (.leaf 273699212) (.leaf 267525202)) (.branch 112 (.leaf 261495639) (.leaf 255606905)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 249855481) (.leaf 244237948)) (.branch 116 (.leaf 238750982) (.leaf 233391350))) (.branch 119 (.branch 118 (.leaf 228155910) (.leaf 223041605)) (.branch 120 (.leaf 218045462) (.leaf 213164589)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 882).prefactor = (1170913089601371/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 882).cutoff/(generalMeanRows 882).c)).2 =
    (171729543960397/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 882).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 882).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 882).q*(generalMeanRows 882).c/2-2 = (6989/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable282.value]
    have hcontinuation : (generalMeanRows 882).q*(generalMeanRows 882).cutoff/2-2 = (80/39:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable279.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 882).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 882

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 882).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 882).criticalRate j.val*(generalMeanRows 882).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 882).c*(generalMeanRows 882).criticalPoint j.val)).2-
      (generalMeanRows 882).J/2-(generalMeanRows 882).error (generalMeanGrid j.val)+
      (generalMeanRows 882).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 882).c)).2-
      (generalMeanRows 882).J/2-(generalMeanRows 882).error 4 := by
  have he : (generalMeanRows 882).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 882) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 882)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0882

/-! Kernel-checked entropy margins for general spectral rectangle 883. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0883
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5258909693) (.branch 2 (.leaf 5092567367) (.leaf 4933387821))) (.branch 5 (.branch 4 (.leaf 4780966570) (.leaf 4634927722)) (.branch 6 (.leaf 4494921485) (.leaf 4360621931)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4231724995) (.leaf 4107946689)) (.branch 10 (.leaf 3989021483) (.leaf 3874700853))) (.branch 13 (.branch 12 (.leaf 3764751965) (.leaf 3658956482)) (.branch 14 (.leaf 3557109479) (.leaf 3459018459))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3364502454) (.branch 17 (.leaf 3273391200) (.leaf 3185524391))) (.branch 20 (.branch 19 (.leaf 3100750983) (.leaf 3018928568)) (.branch 21 (.leaf 2939922786) (.leaf 2863606793)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2789860765) (.leaf 2718571442)) (.branch 25 (.leaf 2649631709) (.leaf 2582940201))) (.branch 28 (.branch 27 (.leaf 2518400947) (.leaf 2455923031)) (.branch 29 (.leaf 2395420282) (.leaf 2336810983)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2280017605) (.branch 32 (.leaf 2224966558) (.leaf 2171587951))) (.branch 35 (.branch 34 (.leaf 2119815380) (.leaf 2069585726)) (.branch 36 (.leaf 2020838960) (.leaf 1973517971)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1927568398) (.leaf 1882938477)) (.branch 40 (.leaf 1839578893) (.leaf 1797442647))) (.branch 43 (.branch 42 (.leaf 1756484925) (.leaf 1716662983)) (.branch 44 (.leaf 1677936033) (.leaf 1640265137))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1603613106) (.branch 47 (.leaf 1567944414) (.leaf 1533225104))) (.branch 50 (.branch 49 (.leaf 1499422707) (.leaf 1466506167)) (.branch 51 (.leaf 1434445767) (.leaf 1403213059)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1372780802) (.leaf 1343122898)) (.branch 55 (.leaf 1314214339) (.leaf 1286031145))) (.branch 58 (.branch 57 (.leaf 1258550323) (.leaf 1231749810)) (.branch 59 (.leaf 1205608431) (.leaf 1180105857))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1155222563) (.branch 62 (.leaf 1130939788) (.leaf 1107239501))) (.branch 65 (.branch 64 (.leaf 1084104365) (.leaf 1061517705)) (.branch 66 (.leaf 1039463478) (.leaf 1017926241)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 996891127) (.leaf 976343816)) (.branch 70 (.leaf 956270511) (.leaf 936657915))) (.branch 73 (.branch 72 (.leaf 917493208) (.leaf 898764025)) (.branch 74 (.leaf 880458440) (.leaf 862564939))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 845072412) (.branch 77 (.leaf 827970125) (.leaf 811247714))) (.branch 80 (.branch 79 (.leaf 794895161) (.leaf 778902785)) (.branch 81 (.leaf 763261226) (.leaf 747961428)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 732994635) (.leaf 718352369)) (.branch 85 (.leaf 704026427) (.leaf 690008862))) (.branch 88 (.branch 87 (.leaf 676291982) (.leaf 662868330)) (.branch 89 (.leaf 649730683) (.leaf 636872037)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 624285602) (.branch 92 (.leaf 611964793) (.leaf 599903221))) (.branch 95 (.branch 94 (.leaf 588094687) (.leaf 576533174)) (.branch 96 (.leaf 565212840) (.leaf 554128012)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 543273181) (.leaf 532642994)) (.branch 100 (.leaf 522232249) (.leaf 512035889))) (.branch 103 (.branch 102 (.leaf 502049000) (.leaf 492266801)) (.branch 104 (.leaf 482684645) (.leaf 473298007))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 464102489) (.leaf 455093807)) (.branch 108 (.leaf 446267793) (.leaf 437620388))) (.branch 111 (.branch 110 (.leaf 429147641) (.leaf 420845702)) (.branch 112 (.leaf 412710821) (.leaf 404739346)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 396927716) (.leaf 389272462)) (.branch 116 (.leaf 381770201) (.leaf 374417637))) (.branch 119 (.branch 118 (.leaf 367211553) (.leaf 360148813)) (.branch 120 (.leaf 353226359) (.leaf 346441207)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 883).prefactor = (2294156003676989/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 883).cutoff/(generalMeanRows 883).c)).2 =
    (200425385278717/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 883).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 883).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 883).q*(generalMeanRows 883).c/2-2 = (1499/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable283.value]
    have hcontinuation : (generalMeanRows 883).q*(generalMeanRows 883).cutoff/2-2 = (40/19:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable284.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 883).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 883

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 883).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 883).criticalRate j.val*(generalMeanRows 883).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 883).c*(generalMeanRows 883).criticalPoint j.val)).2-
      (generalMeanRows 883).J/2-(generalMeanRows 883).error (generalMeanGrid j.val)+
      (generalMeanRows 883).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 883).c)).2-
      (generalMeanRows 883).J/2-(generalMeanRows 883).error 4 := by
  have he : (generalMeanRows 883).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 883) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 883)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0883

/-! Kernel-checked entropy margins for general spectral rectangle 884. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0884
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4959426679) (.branch 2 (.leaf 4789852508) (.leaf 4627756542))) (.branch 5 (.branch 4 (.leaf 4472717947) (.leaf 4324345461)) (.branch 6 (.leaf 4182274812) (.leaf 4046166413)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3915703302) (.leaf 3790589292)) (.branch 10 (.leaf 3670547311) (.leaf 3555317895))) (.branch 13 (.branch 12 (.leaf 3444657833) (.leaf 3338338938)) (.branch 14 (.leaf 3236146927) (.leaf 3137880405))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3043349935) (.branch 17 (.leaf 2952377192) (.leaf 2864794187))) (.branch 20 (.branch 19 (.leaf 2780442554) (.leaf 2699172897)) (.branch 21 (.leaf 2620844190) (.leaf 2545323225)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2472484096) (.leaf 2402207735)) (.branch 25 (.leaf 2334381471) (.leaf 2268898628))) (.branch 28 (.branch 27 (.leaf 2205658155) (.leaf 2144564272)) (.branch 29 (.leaf 2085526155) (.leaf 2028457634)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1973276915) (.branch 32 (.leaf 1919906320) (.leaf 1868272045))) (.branch 35 (.branch 34 (.leaf 1818303938) (.leaf 1769935285)) (.branch 36 (.leaf 1723102616) (.leaf 1677745520)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1633806473) (.leaf 1591230679)) (.branch 40 (.leaf 1549965917) (.leaf 1509962400))) (.branch 43 (.branch 42 (.leaf 1471172647) (.leaf 1433551352)) (.branch 44 (.leaf 1397055272) (.leaf 1361643115))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1327275440) (.branch 47 (.leaf 1293914556) (.leaf 1261524435))) (.branch 50 (.branch 49 (.leaf 1230070623) (.leaf 1199520161)) (.branch 51 (.leaf 1169841508) (.leaf 1141004471)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1112980134) (.leaf 1085740798)) (.branch 55 (.leaf 1059259919) (.leaf 1033512052))) (.branch 58 (.branch 57 (.leaf 1008472794) (.leaf 984118738)) (.branch 59 (.leaf 960427424) (.leaf 937377291))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 914947636) (.branch 62 (.leaf 893118574) (.leaf 871870999))) (.branch 65 (.branch 64 (.leaf 851186547) (.leaf 831047564)) (.branch 66 (.leaf 811437070) (.leaf 792338730)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 773736826) (.leaf 755616227)) (.branch 70 (.leaf 737962362) (.leaf 720761199))) (.branch 73 (.branch 72 (.leaf 703999218) (.leaf 687663388)) (.branch 74 (.leaf 671741149) (.leaf 656220389))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 641089424) (.branch 77 (.leaf 626336982) (.leaf 611952186))) (.branch 80 (.branch 79 (.leaf 597924533) (.leaf 584243884)) (.branch 81 (.leaf 570900444) (.leaf 557884753)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 545187665) (.leaf 532800343)) (.branch 85 (.leaf 520714241) (.leaf 508921096))) (.branch 88 (.branch 87 (.leaf 497412914) (.leaf 486181960)) (.branch 89 (.leaf 475220749) (.leaf 464522034)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 454078802) (.branch 92 (.leaf 443884256) (.leaf 433931816))) (.branch 95 (.branch 94 (.leaf 424215105) (.leaf 414727943)) (.branch 96 (.leaf 405464342) (.leaf 396418494)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 387584767) (.leaf 378957701)) (.branch 100 (.leaf 370531997) (.leaf 362302514))) (.branch 103 (.branch 102 (.leaf 354264264) (.leaf 346412404)) (.branch 104 (.leaf 338742233) (.leaf 331249187))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 323928831) (.leaf 316776860)) (.branch 108 (.leaf 309789090) (.leaf 302961456))) (.branch 111 (.branch 110 (.leaf 296290008) (.leaf 289770904)) (.branch 112 (.leaf 283400414) (.leaf 277174905)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 271090850) (.leaf 265144815)) (.branch 116 (.leaf 259333460) (.leaf 253653537))) (.branch 119 (.branch 118 (.leaf 248101885) (.leaf 242675427)) (.branch 120 (.leaf 237371169) (.leaf 232186197)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 884).prefactor = (4724138325031259/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 884).cutoff/(generalMeanRows 884).c)).2 =
    (180525478048301/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 884).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 884).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 884).q*(generalMeanRows 884).c/2-2 = (6831/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable285.value]
    have hcontinuation : (generalMeanRows 884).q*(generalMeanRows 884).cutoff/2-2 = (7598/3627:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable281.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 884).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 884

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 884).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 884).criticalRate j.val*(generalMeanRows 884).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 884).c*(generalMeanRows 884).criticalPoint j.val)).2-
      (generalMeanRows 884).J/2-(generalMeanRows 884).error (generalMeanGrid j.val)+
      (generalMeanRows 884).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 884).c)).2-
      (generalMeanRows 884).J/2-(generalMeanRows 884).error 4 := by
  have he : (generalMeanRows 884).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 884) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 884)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0884

/-! Kernel-checked entropy margins for general spectral rectangle 885. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0885
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4949075893) (.branch 2 (.leaf 4777664934) (.leaf 4613845096))) (.branch 5 (.branch 4 (.leaf 4457189345) (.leaf 4307300624)) (.branch 6 (.leaf 4163809235) (.leaf 4026370510)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3894662716) (.leaf 3768385187)) (.branch 10 (.leaf 3647256637) (.leaf 3531013635))) (.branch 13 (.branch 12 (.leaf 3419409233) (.leaf 3312211717)) (.branch 14 (.leaf 3209203476) (.leaf 3110179969))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3014948785) (.branch 17 (.leaf 2923328785) (.leaf 2835149314))) (.branch 20 (.branch 19 (.leaf 2750249482) (.leaf 2668477498)) (.branch 21 (.leaf 2589690064) (.leaf 2513751814)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2440534795) (.leaf 2369917991)) (.branch 25 (.leaf 2301786881) (.leaf 2236033030))) (.branch 28 (.branch 27 (.leaf 2172553709) (.leaf 2111251546)) (.branch 29 (.leaf 2052034197) (.leaf 1994814045)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1939507917) (.branch 32 (.leaf 1886036820) (.leaf 1834325699))) (.branch 35 (.branch 34 (.leaf 1784303203) (.leaf 1735901478)) (.branch 36 (.leaf 1689055966) (.leaf 1643705215)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1599790710) (.leaf 1557256705)) (.branch 40 (.leaf 1516050074) (.leaf 1476120166))) (.branch 43 (.branch 42 (.leaf 1437418672) (.leaf 1399899496)) (.branch 44 (.leaf 1363518640) (.leaf 1328234090))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1294005714) (.branch 47 (.leaf 1260795162) (.leaf 1228565774))) (.branch 50 (.branch 49 (.leaf 1197282493) (.leaf 1166911781)) (.branch 51 (.leaf 1137421547) (.leaf 1108781068)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1080960925) (.leaf 1053932934)) (.branch 55 (.leaf 1027670089) (.leaf 1002146503))) (.branch 58 (.branch 57 (.leaf 977337351) (.leaf 953218821)) (.branch 59 (.leaf 929768065) (.leaf 906963153))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 884783028) (.branch 62 (.leaf 863207467) (.leaf 842217041))) (.branch 65 (.branch 64 (.leaf 821793076) (.leaf 801917622)) (.branch 66 (.leaf 782573417) (.leaf 763743856)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 745412963) (.leaf 727565359)) (.branch 70 (.leaf 710186240) (.leaf 693261349))) (.branch 73 (.branch 72 (.leaf 676776949) (.leaf 660719808)) (.branch 74 (.leaf 645077167) (.leaf 629836728))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 614986631) (.branch 77 (.leaf 600515434) (.leaf 586412097))) (.branch 80 (.branch 79 (.leaf 572665965) (.leaf 559266751)) (.branch 81 (.leaf 546204522) (.leaf 533469683)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 521052964) (.leaf 508945407)) (.branch 85 (.leaf 497138353) (.leaf 485623430))) (.branch 88 (.branch 87 (.leaf 474392541) (.leaf 463437854)) (.branch 89 (.leaf 452751792) (.leaf 442327021)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 432156444) (.branch 92 (.leaf 422233187) (.leaf 412550597))) (.branch 95 (.branch 94 (.leaf 403102226) (.leaf 393881830)) (.branch 96 (.leaf 384883357) (.leaf 376100942)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 367528899) (.leaf 359161716)) (.branch 100 (.leaf 350994048) (.leaf 343020708))) (.branch 103 (.branch 102 (.leaf 335236666) (.leaf 327637040)) (.branch 104 (.leaf 320217095) (.leaf 312972231))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 305897984) (.leaf 298990020)) (.branch 108 (.leaf 292244130) (.leaf 285656223))) (.branch 111 (.branch 110 (.leaf 279222329) (.leaf 272938587)) (.branch 112 (.leaf 266801248) (.leaf 260806664)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 254951294) (.leaf 249231691)) (.branch 116 (.leaf 243644507) (.leaf 238186483))) (.branch 119 (.branch 118 (.leaf 232854450) (.leaf 227645327)) (.branch 120 (.leaf 222556115) (.leaf 217583897)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 885).prefactor = (598713939685509/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 885).cutoff/(generalMeanRows 885).c)).2 =
    (354154377037541/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 885).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 885).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 885).q*(generalMeanRows 885).c/2-2 = (6989/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable282.value]
    have hcontinuation : (generalMeanRows 885).q*(generalMeanRows 885).cutoff/2-2 = (7598/3627:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable281.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 885).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 885

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 885).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 885).criticalRate j.val*(generalMeanRows 885).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 885).c*(generalMeanRows 885).criticalPoint j.val)).2-
      (generalMeanRows 885).J/2-(generalMeanRows 885).error (generalMeanGrid j.val)+
      (generalMeanRows 885).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 885).c)).2-
      (generalMeanRows 885).J/2-(generalMeanRows 885).error 4 := by
  have he : (generalMeanRows 885).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 885) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 885)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0885

/-! Kernel-checked entropy margins for general spectral rectangle 886. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0886
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5162086628) (.branch 2 (.leaf 4994153649) (.leaf 4833505556))) (.branch 5 (.branch 4 (.leaf 4679731750) (.leaf 4532450598)) (.branch 6 (.leaf 4391306904) (.leaf 4255969648)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4126129962) (.leaf 4001499321)) (.branch 10 (.leaf 3881807901) (.leaf 3766803114))) (.branch 13 (.branch 12 (.leaf 3656248272) (.leaf 3549921382)) (.branch 14 (.leaf 3447614047) (.leaf 3349130468))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3254286535) (.branch 17 (.leaf 3162908994) (.leaf 3074834690))) (.branch 20 (.branch 19 (.leaf 2989909860) (.leaf 2907989503)) (.branch 21 (.leaf 2828936783) (.leaf 2752622489)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2678924538) (.leaf 2607727507)) (.branch 25 (.leaf 2538922211) (.leaf 2472405305))) (.branch 28 (.branch 27 (.leaf 2408078919) (.leaf 2345850321)) (.branch 29 (.leaf 2285631596) (.leaf 2227339359)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2170894479) (.branch 32 (.leaf 2116221826) (.leaf 2063250036))) (.branch 35 (.branch 34 (.leaf 2011911289) (.leaf 1962141106)) (.branch 36 (.leaf 1913878152) (.leaf 1867064061)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1821643270) (.leaf 1777562853)) (.branch 40 (.leaf 1734772383) (.leaf 1693223792))) (.branch 43 (.branch 42 (.leaf 1652871237) (.leaf 1613670986)) (.branch 44 (.leaf 1575581299) (.leaf 1538562323))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1502575992) (.branch 47 (.leaf 1467585932) (.leaf 1433557372))) (.branch 50 (.branch 49 (.leaf 1400457063) (.leaf 1368253195)) (.branch 51 (.leaf 1336915328) (.leaf 1306414318)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1276722253) (.leaf 1247812393)) (.branch 55 (.leaf 1219659108) (.leaf 1192237826))) (.branch 58 (.branch 57 (.leaf 1165524978) (.leaf 1139497952)) (.branch 59 (.leaf 1114135045) (.leaf 1089415417))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1065319055) (.branch 62 (.leaf 1041826727) (.leaf 1018919952))) (.branch 65 (.branch 64 (.leaf 996580957) (.leaf 974792653)) (.branch 66 (.leaf 953538594) (.leaf 932802955)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 912570499) (.leaf 892826553)) (.branch 70 (.leaf 873556979) (.leaf 854748155))) (.branch 73 (.branch 72 (.leaf 836386949) (.leaf 818460696)) (.branch 74 (.leaf 800957183) (.leaf 783864623))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 767171639) (.branch 77 (.leaf 750867249) (.leaf 734940845))) (.branch 80 (.branch 79 (.leaf 719382181) (.leaf 704181354)) (.branch 81 (.leaf 689328793) (.leaf 674815244)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 660631756) (.leaf 646769669)) (.branch 85 (.leaf 633220605) (.leaf 619976453))) (.branch 88 (.branch 87 (.leaf 607029360) (.leaf 594371721)) (.branch 89 (.leaf 581996168) (.leaf 569895563)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 558062986) (.branch 92 (.leaf 546491731) (.leaf 535175292))) (.branch 95 (.branch 94 (.leaf 524107361) (.leaf 513281818)) (.branch 96 (.leaf 502692725) (.leaf 492334316)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 482200995) (.leaf 472287329)) (.branch 100 (.leaf 462588040) (.leaf 453098001))) (.branch 103 (.branch 102 (.leaf 443812230) (.leaf 434725886)) (.branch 104 (.leaf 425834263) (.leaf 417132785))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 408617004) (.leaf 400282591)) (.branch 108 (.leaf 392125337) (.leaf 384141146))) (.branch 111 (.branch 110 (.leaf 376326033) (.leaf 368676118)) (.branch 112 (.leaf 361187623) (.leaf 353856873)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 346680286) (.leaf 339654375)) (.branch 116 (.leaf 332775742) (.leaf 326041078))) (.branch 119 (.branch 118 (.leaf 319447157) (.leaf 312990837)) (.branch 120 (.leaf 306669053) (.leaf 300478819)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 886).prefactor = (4651664009524089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 886).cutoff/(generalMeanRows 886).c)).2 =
    (386766030675697/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 886).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 886).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 886).q*(generalMeanRows 886).c/2-2 = (1577/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable272.value]
    have hcontinuation : (generalMeanRows 886).q*(generalMeanRows 886).cutoff/2-2 = (40/19:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable284.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 886).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 886

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 886).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 886).criticalRate j.val*(generalMeanRows 886).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 886).c*(generalMeanRows 886).criticalPoint j.val)).2-
      (generalMeanRows 886).J/2-(generalMeanRows 886).error (generalMeanGrid j.val)+
      (generalMeanRows 886).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 886).c)).2-
      (generalMeanRows 886).J/2-(generalMeanRows 886).error 4 := by
  have he : (generalMeanRows 886).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 886) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 886)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0886

/-! Kernel-checked entropy margins for general spectral rectangle 887. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0887
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5150074506) (.branch 2 (.leaf 4980228368) (.leaf 4817778769))) (.branch 5 (.branch 4 (.leaf 4662309136) (.leaf 4513432256)) (.branch 6 (.leaf 4370787708) (.leaf 4234039575)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4102874394) (.leaf 3976999317)) (.branch 10 (.leaf 3856140460) (.leaf 3740041406))) (.branch 13 (.branch 12 (.leaf 3628461860) (.leaf 3521176422)) (.branch 14 (.leaf 3417973479) (.leaf 3318654191))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3223031571) (.branch 17 (.leaf 3130929639) (.leaf 3042182657))) (.branch 20 (.branch 19 (.leaf 2956634414) (.leaf 2874137583)) (.branch 21 (.leaf 2794553122) (.leaf 2717749722)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2643603305) (.leaf 2571996550)) (.branch 25 (.leaf 2502818468) (.leaf 2435963993))) (.branch 28 (.branch 27 (.leaf 2371333617) (.leaf 2308833045)) (.branch 29 (.leaf 2248372873) (.leaf 2189868294)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2133238822) (.branch 32 (.leaf 2078408030) (.leaf 2025303319))) (.branch 35 (.branch 34 (.leaf 1973855686) (.leaf 1923999521)) (.branch 36 (.leaf 1875672410) (.leaf 1828814956)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1783370604) (.leaf 1739285485)) (.branch 40 (.leaf 1696508266) (.leaf 1654990012))) (.branch 43 (.branch 42 (.leaf 1614684052) (.leaf 1575545857)) (.branch 44 (.leaf 1537532926) (.leaf 1500604677))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1464722345) (.branch 47 (.leaf 1429848886) (.leaf 1395948886))) (.branch 50 (.branch 49 (.leaf 1362988481) (.leaf 1330935269)) (.branch 51 (.leaf 1299758244) (.leaf 1269427719)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1239915261) (.leaf 1211193631)) (.branch 55 (.leaf 1183236718) (.leaf 1156019490))) (.branch 58 (.branch 57 (.leaf 1129517938) (.leaf 1103709025)) (.branch 59 (.leaf 1078570641) (.leaf 1054081559))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1030221388) (.branch 62 (.leaf 1006970540) (.leaf 984310187))) (.branch 65 (.branch 64 (.leaf 962222228) (.leaf 940689254)) (.branch 66 (.leaf 919694516) (.leaf 899221897)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 879255880) (.leaf 859781522)) (.branch 70 (.leaf 840784428) (.leaf 822250729))) (.branch 73 (.branch 72 (.leaf 804167056) (.leaf 786520516)) (.branch 74 (.leaf 769298678) (.leaf 752489545))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 736081543) (.branch 77 (.leaf 720063494) (.leaf 704424609))) (.branch 80 (.branch 79 (.leaf 689154464) (.leaf 674242989)) (.branch 81 (.leaf 659680449) (.leaf 645457437)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 631564853) (.leaf 617993897)) (.branch 85 (.leaf 604736055) (.leaf 591783085))) (.branch 88 (.branch 87 (.leaf 579127011) (.leaf 566760110)) (.branch 89 (.leaf 554674901) (.leaf 542864138)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 531320798) (.branch 92 (.leaf 520038076) (.leaf 509009374))) (.branch 95 (.branch 94 (.leaf 498228295) (.leaf 487688632)) (.branch 96 (.leaf 477384367) (.leaf 467309657)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 457458834) (.leaf 447826394)) (.branch 100 (.leaf 438406994) (.leaf 429195443))) (.branch 103 (.branch 102 (.leaf 420186702) (.leaf 411375872)) (.branch 104 (.leaf 402758195) (.leaf 394329045))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 386083925) (.leaf 378018463)) (.branch 108 (.leaf 370128408) (.leaf 362409624))) (.branch 111 (.branch 110 (.leaf 354858088) (.leaf 347469887)) (.branch 112 (.leaf 340241211) (.leaf 333168352)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 326247702) (.leaf 319475747)) (.branch 116 (.leaf 312849065) (.leaf 306364325))) (.branch 119 (.branch 118 (.leaf 300018279) (.leaf 293807767)) (.branch 120 (.leaf 287729707) (.leaf 281781098)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 887).prefactor = (2357945364528521/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 887).cutoff/(generalMeanRows 887).c)).2 =
    (189898680679801/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 887).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 887).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 887).q*(generalMeanRows 887).c/2-2 = (101/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable286.value]
    have hcontinuation : (generalMeanRows 887).q*(generalMeanRows 887).cutoff/2-2 = (40/19:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable284.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 887).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 887

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 887).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 887).criticalRate j.val*(generalMeanRows 887).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 887).c*(generalMeanRows 887).criticalPoint j.val)).2-
      (generalMeanRows 887).J/2-(generalMeanRows 887).error (generalMeanGrid j.val)+
      (generalMeanRows 887).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 887).c)).2-
      (generalMeanRows 887).J/2-(generalMeanRows 887).error 4 := by
  have he : (generalMeanRows 887).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 887) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 887)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0887

/-! Kernel-checked entropy margins for general spectral rectangle 888. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0888
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4939112866) (.branch 2 (.leaf 4765873299) (.leaf 4600338894))) (.branch 5 (.branch 4 (.leaf 4442076307) (.leaf 4290682582)) (.branch 6 (.leaf 4145782503) (.leaf 4007026229)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3874087176) (.leaf 3746660122)) (.branch 10 (.leaf 3624459494) (.leaf 3507217826))) (.branch 13 (.branch 12 (.leaf 3394684369) (.leaf 3286623826)) (.branch 14 (.leaf 3182815201) (.leaf 3083050758))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2987135062) (.branch 17 (.leaf 2894884117) (.leaf 2806124562))) (.branch 20 (.branch 19 (.leaf 2720692939) (.leaf 2638435030)) (.branch 21 (.leaf 2559205231) (.leaf 2482865986)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2409287268) (.leaf 2338346085)) (.branch 25 (.leaf 2269926041) (.leaf 2203916918))) (.branch 28 (.branch 27 (.leaf 2140214291) (.leaf 2078719172)) (.branch 29 (.leaf 2019337682) (.leaf 1961980741)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1906563781) (.branch 32 (.leaf 1853006482) (.leaf 1801232520))) (.branch 35 (.branch 34 (.leaf 1751169340) (.leaf 1702747937)) (.branch 36 (.leaf 1655902652) (.leaf 1610570988)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1566693428) (.leaf 1524213273)) (.branch 40 (.leaf 1483076486) (.leaf 1443231546))) (.branch 43 (.branch 42 (.leaf 1404629313) (.leaf 1367222898)) (.branch 44 (.leaf 1330967544) (.leaf 1295820515))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1261740986) (.branch 47 (.leaf 1228689946) (.leaf 1196630103))) (.branch 50 (.branch 49 (.leaf 1165525797) (.leaf 1135342915)) (.branch 51 (.leaf 1106048813) (.leaf 1077612241)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1050003278) (.leaf 1023193258)) (.branch 55 (.leaf 997154716) (.leaf 971861325))) (.branch 58 (.branch 57 (.leaf 947287839) (.leaf 923410048)) (.branch 59 (.leaf 900204718) (.leaf 877649554))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 855723150) (.branch 62 (.leaf 834404946) (.leaf 813675196))) (.branch 65 (.branch 64 (.leaf 793514921) (.leaf 773905880)) (.branch 66 (.leaf 754830533) (.leaf 736272011)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 718214082) (.leaf 700641130)) (.branch 70 (.leaf 683538117) (.leaf 666890568))) (.branch 73 (.branch 72 (.leaf 650684537) (.leaf 634906591)) (.branch 74 (.leaf 619543783) (.leaf 604583633))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 590014109) (.branch 77 (.leaf 575823605) (.leaf 562000925))) (.branch 80 (.branch 79 (.leaf 548535265) (.leaf 535416198)) (.branch 81 (.leaf 522633656) (.leaf 510177918)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 498039593) (.leaf 486209609)) (.branch 85 (.leaf 474679197) (.leaf 463439883))) (.branch 88 (.branch 87 (.leaf 452483472) (.leaf 441802043)) (.branch 89 (.leaf 431387928) (.leaf 421233715)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 411332227) (.branch 92 (.leaf 401676518) (.leaf 392259866))) (.branch 95 (.branch 94 (.leaf 383075759) (.leaf 374117892)) (.branch 96 (.leaf 365380157) (.leaf 356856636)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 348541593) (.leaf 340429470)) (.branch 100 (.leaf 332514877) (.leaf 324792590))) (.branch 103 (.branch 102 (.leaf 317257540) (.leaf 309904813)) (.branch 104 (.leaf 302729640) (.leaf 295727393))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 288893582) (.leaf 282223848)) (.branch 108 (.leaf 275713960) (.leaf 269359810))) (.branch 111 (.branch 110 (.leaf 263157408) (.leaf 257102878)) (.branch 112 (.leaf 251192456) (.leaf 245422486)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 239789413) (.leaf 234289784)) (.branch 116 (.leaf 228920243) (.leaf 223677526))) (.branch 119 (.branch 118 (.leaf 218558460) (.leaf 213559963)) (.branch 120 (.leaf 208679032) (.leaf 203912752)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 888).prefactor = (4856194895725827/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 888).cutoff/(generalMeanRows 888).c)).2 =
    (10853282349749/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 888).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 888).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 888).q*(generalMeanRows 888).cutoff/2-2 = (7598/3627:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable281.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 888).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 888

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 888).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 888).criticalRate j.val*(generalMeanRows 888).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 888).c*(generalMeanRows 888).criticalPoint j.val)).2-
      (generalMeanRows 888).J/2-(generalMeanRows 888).error (generalMeanGrid j.val)+
      (generalMeanRows 888).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 888).c)).2-
      (generalMeanRows 888).J/2-(generalMeanRows 888).error 4 := by
  have he : (generalMeanRows 888).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 888) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 888)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0888

/-! Kernel-checked entropy margins for general spectral rectangle 889. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0889
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5299920481) (.branch 2 (.leaf 5129872564) (.leaf 4967218728))) (.branch 5 (.branch 4 (.leaf 4811538425) (.leaf 4662440960)) (.branch 6 (.leaf 4519562876) (.leaf 4382565625)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4251133482) (.leaf 4124971671)) (.branch 10 (.leaf 4003804680) (.leaf 3887374744))) (.branch 13 (.branch 12 (.leaf 3775440460) (.leaf 3667775552)) (.branch 14 (.leaf 3564167726) (.leaf 3464417648))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3368338000) (.branch 17 (.leaf 3275752619) (.leaf 3186495712))) (.branch 20 (.branch 19 (.leaf 3100411137) (.leaf 3017351737)) (.branch 21 (.leaf 2937178734) (.leaf 2859761169)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2784975382) (.leaf 2712704540)) (.branch 25 (.leaf 2642838190) (.leaf 2575271858))) (.branch 28 (.branch 27 (.leaf 2509906667) (.leaf 2446648987)) (.branch 29 (.leaf 2385410110) (.leaf 2326105950)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2268656760) (.branch 32 (.leaf 2212986872) (.leaf 2159024451))) (.branch 35 (.branch 34 (.leaf 2106701275) (.leaf 2055952512)) (.branch 36 (.leaf 2006716536) (.leaf 1958934731)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1912551324) (.leaf 1867513224)) (.branch 40 (.leaf 1823769871) (.leaf 1781273089))) (.branch 43 (.branch 42 (.leaf 1739976964) (.leaf 1699837709)) (.branch 44 (.leaf 1660813555) (.leaf 1622864639))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1585952899) (.branch 47 (.leaf 1550041984) (.leaf 1515097157))) (.branch 50 (.branch 49 (.leaf 1481085211) (.leaf 1447974393)) (.branch 51 (.leaf 1415734323) (.leaf 1384335927)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1353751369) (.leaf 1323953986)) (.branch 55 (.leaf 1294918232) (.leaf 1266619619))) (.branch 58 (.branch 57 (.leaf 1239034666) (.leaf 1212140848)) (.branch 59 (.leaf 1185916551) (.leaf 1160341023))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1135394339) (.branch 62 (.leaf 1111057355) (.leaf 1087311673))) (.branch 65 (.branch 64 (.leaf 1064139605) (.leaf 1041524141)) (.branch 66 (.leaf 1019448916) (.leaf 997898180)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 976856770) (.leaf 956310082)) (.branch 70 (.leaf 936244046) (.leaf 916645104))) (.branch 73 (.branch 72 (.leaf 897500184) (.leaf 878796679)) (.branch 74 (.leaf 860522427) (.leaf 842665692))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 825215146) (.branch 77 (.leaf 808159847) (.leaf 791489228))) (.branch 80 (.branch 79 (.leaf 775193078) (.leaf 759261528)) (.branch 81 (.leaf 743685033) (.leaf 728454367)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 713560599) (.leaf 698995091)) (.branch 85 (.leaf 684749479) (.leaf 670815664))) (.branch 88 (.branch 87 (.leaf 657185802) (.leaf 643852296)) (.branch 89 (.leaf 630807780) (.leaf 618045118)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 605557387) (.branch 92 (.leaf 593337875) (.leaf 581380071))) (.branch 95 (.branch 94 (.leaf 569677655) (.leaf 558224495)) (.branch 96 (.leaf 547014638) (.leaf 536042302)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 525301870) (.leaf 514787889)) (.branch 100 (.leaf 504495057) (.leaf 494418221))) (.branch 103 (.branch 102 (.leaf 484552373) (.leaf 474892642)) (.branch 104 (.leaf 465434292) (.leaf 456172714))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 447103425) (.leaf 438222064)) (.branch 108 (.leaf 429524382) (.leaf 421006247))) (.branch 111 (.branch 110 (.leaf 412663633) (.leaf 404492619)) (.branch 112 (.leaf 396489389) (.leaf 388650221)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 380971491) (.leaf 373449667)) (.branch 116 (.leaf 366081306) (.leaf 358863051))) (.branch 119 (.branch 118 (.leaf 351791631) (.leaf 344863853)) (.branch 120 (.leaf 338076607) (.leaf 331426856)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 889).prefactor = (593821485188663/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 889).cutoff/(generalMeanRows 889).c)).2 =
    (40447889245109/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 889).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 889).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 889).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 889

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 889).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 889).criticalRate j.val*(generalMeanRows 889).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 889).c*(generalMeanRows 889).criticalPoint j.val)).2-
      (generalMeanRows 889).J/2-(generalMeanRows 889).error (generalMeanGrid j.val)+
      (generalMeanRows 889).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 889).c)).2-
      (generalMeanRows 889).J/2-(generalMeanRows 889).error 4 := by
  have he : (generalMeanRows 889).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 889) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 889)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0889

/-! Kernel-checked entropy margins for general spectral rectangle 890. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0890
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5057391256) (.branch 2 (.leaf 4886111713) (.leaf 4722351761))) (.branch 5 (.branch 4 (.leaf 4565688398) (.leaf 4415728371)) (.branch 6 (.leaf 4272105580) (.leaf 4134478758)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4002529397) (.leaf 3875959886)) (.branch 10 (.leaf 3754491838) (.leaf 3637864576))) (.branch 13 (.branch 12 (.leaf 3525833769) (.leaf 3418170190)) (.branch 14 (.leaf 3314658597) (.leaf 3215096700))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3119294237) (.branch 17 (.leaf 3027072111) (.leaf 2938261616))) (.branch 20 (.branch 19 (.leaf 2852703719) (.leaf 2770248399)) (.branch 21 (.leaf 2690754047) (.leaf 2614086909)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2540120567) (.leaf 2468735471)) (.branch 25 (.leaf 2399818500) (.leaf 2333262552))) (.branch 28 (.branch 27 (.leaf 2268966172) (.leaf 2206833204)) (.branch 29 (.leaf 2146772462) (.leaf 2088697436)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2032526007) (.branch 32 (.leaf 1978180190) (.leaf 1925585888))) (.branch 35 (.branch 34 (.leaf 1874672668) (.leaf 1825373548)) (.branch 36 (.leaf 1777624800) (.leaf 1731365766)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1686538686) (.leaf 1643088534)) (.branch 40 (.leaf 1600962868) (.leaf 1560111691))) (.branch 43 (.branch 42 (.leaf 1520487312) (.leaf 1482044227)) (.branch 44 (.leaf 1444738997) (.leaf 1408530144))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1373378041) (.branch 47 (.leaf 1339244819) (.leaf 1306094274))) (.branch 50 (.branch 49 (.leaf 1273891781) (.leaf 1242604215)) (.branch 51 (.leaf 1212199872) (.leaf 1182648396)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1153920716) (.leaf 1125988978)) (.branch 55 (.leaf 1098826487) (.leaf 1072407646))) (.branch 58 (.branch 57 (.leaf 1046707908) (.leaf 1021703721)) (.branch 59 (.leaf 997372481) (.leaf 973692487))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 950642899) (.branch 62 (.leaf 928203694) (.leaf 906355632))) (.branch 65 (.branch 64 (.leaf 885080216) (.leaf 864359659)) (.branch 66 (.leaf 844176853) (.leaf 824515334)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 805359257) (.leaf 786693365)) (.branch 70 (.leaf 768502966) (.leaf 750773902))) (.branch 73 (.branch 72 (.leaf 733492533) (.leaf 716645710)) (.branch 74 (.leaf 700220752) (.leaf 684205430))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 668587945) (.branch 77 (.leaf 653356911) (.leaf 638501336))) (.branch 80 (.branch 79 (.leaf 624010606) (.leaf 609874470)) (.branch 81 (.leaf 596083025) (.leaf 582626699)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 569496242) (.leaf 556682709)) (.branch 85 (.leaf 544177450) (.leaf 531972097))) (.branch 88 (.branch 87 (.leaf 520058553) (.leaf 508428983)) (.branch 89 (.leaf 497075800) (.leaf 485991660)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 475169449) (.branch 92 (.leaf 464602275) (.leaf 454283461))) (.branch 95 (.branch 94 (.leaf 444206536) (.leaf 434365227)) (.branch 96 (.leaf 424753451) (.leaf 415365310)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 406195083) (.leaf 397237219)) (.branch 100 (.leaf 388486331) (.leaf 379937192))) (.branch 103 (.branch 102 (.leaf 371584727) (.leaf 363424009)) (.branch 104 (.leaf 355450253) (.leaf 347658811))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 340045168) (.leaf 332604938)) (.branch 108 (.leaf 325333857) (.leaf 318227782))) (.branch 111 (.branch 110 (.leaf 311282685) (.leaf 304494648)) (.branch 112 (.leaf 297859864) (.leaf 291374629)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 285035340) (.leaf 278838490)) (.branch 116 (.leaf 272780670) (.leaf 266858559))) (.branch 119 (.branch 118 (.leaf 261068928) (.leaf 255408632)) (.branch 120 (.leaf 249874608) (.leaf 244463876)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 890).prefactor = (4781004243400087/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 890).cutoff/(generalMeanRows 890).c)).2 =
    (73200807845453/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 890).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 890).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 890).q*(generalMeanRows 890).c/2-2 = (847/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable287.value]
    have hcontinuation : (generalMeanRows 890).q*(generalMeanRows 890).cutoff/2-2 = (40/19:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable284.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 890).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 890

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 890).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 890).criticalRate j.val*(generalMeanRows 890).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 890).c*(generalMeanRows 890).criticalPoint j.val)).2-
      (generalMeanRows 890).J/2-(generalMeanRows 890).error (generalMeanGrid j.val)+
      (generalMeanRows 890).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 890).c)).2-
      (generalMeanRows 890).J/2-(generalMeanRows 890).error 4 := by
  have he : (generalMeanRows 890).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 890) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 890)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0890

/-! Kernel-checked entropy margins for general spectral rectangle 891. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0891
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5127219956) (.branch 2 (.leaf 4953575512) (.leaf 4787554485))) (.branch 5 (.branch 4 (.leaf 4628728030) (.leaf 4476697467)) (.branch 6 (.leaf 4331091639) (.leaf 4191564568)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4057793348) (.leaf 3929476260)) (.branch 10 (.leaf 3806331071) (.leaf 3688093507))) (.branch 13 (.branch 12 (.leaf 3574515861) (.leaf 3465365744)) (.branch 14 (.leaf 3360424939) (.leaf 3259488366))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3162363133) (.branch 17 (.leaf 3068867673) (.leaf 2978830949))) (.branch 20 (.branch 19 (.leaf 2892091732) (.leaf 2808497930)) (.branch 21 (.leaf 2727905980) (.leaf 2650180278)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2575192664) (.leaf 2502821936)) (.branch 25 (.leaf 2432953410) (.leaf 2365478507))) (.branch 28 (.branch 27 (.leaf 2300294371) (.leaf 2237303516)) (.branch 29 (.leaf 2176413500) (.leaf 2117536618)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2060589616) (.branch 32 (.leaf 2005493432) (.leaf 1952172947))) (.branch 35 (.branch 34 (.leaf 1900556755) (.leaf 1850576949)) (.branch 36 (.leaf 1802168922) (.leaf 1755271178)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1709825158) (.leaf 1665775079)) (.branch 40 (.leaf 1623067774) (.leaf 1581652554))) (.branch 43 (.branch 42 (.leaf 1541481071) (.leaf 1502507192)) (.branch 44 (.leaf 1464686880) (.leaf 1427978082))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1392340624) (.branch 47 (.leaf 1357736116) (.leaf 1324127853))) (.branch 50 (.branch 49 (.leaf 1291480732) (.leaf 1259761171)) (.branch 51 (.leaf 1228937026) (.leaf 1198977526)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1169853196) (.leaf 1141535797)) (.branch 55 (.leaf 1113998266) (.leaf 1087214654))) (.branch 58 (.branch 57 (.leaf 1061160073) (.leaf 1035810646)) (.branch 59 (.leaf 1011143459) (.leaf 987136509))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 963768669) (.branch 62 (.leaf 941019641) (.leaf 918869917))) (.branch 65 (.branch 64 (.leaf 897300746) (.leaf 876294095)) (.branch 66 (.leaf 855832619) (.leaf 835899629)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 816479059) (.leaf 797555443)) (.branch 70 (.leaf 779113883) (.leaf 761140030))) (.branch 73 (.branch 72 (.leaf 743620053) (.leaf 726540621)) (.branch 74 (.leaf 709888879) (.leaf 693652430))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 677819311) (.branch 77 (.leaf 662377978) (.leaf 647317288))) (.branch 80 (.branch 79 (.leaf 632626481) (.leaf 618295164)) (.branch 81 (.leaf 604313296) (.leaf 590671175)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 577359423) (.leaf 564368970)) (.branch 85 (.leaf 551691047) (.leaf 539317172))) (.branch 88 (.branch 87 (.leaf 527239135) (.leaf 515448992)) (.branch 89 (.leaf 503939053) (.leaf 492701872)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 481730235) (.branch 92 (.leaf 471017158) (.leaf 460555869))) (.branch 95 (.branch 94 (.leaf 450339810) (.leaf 440362619)) (.branch 96 (.leaf 430618131) (.leaf 421100366)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 411803523) (.leaf 402721975)) (.branch 100 (.leaf 393850261) (.leaf 385183082))) (.branch 103 (.branch 102 (.leaf 376715293) (.leaf 368441898)) (.branch 104 (.leaf 360358046) (.leaf 352459025))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 344740259) (.leaf 337197300)) (.branch 108 (.leaf 329825825) (.leaf 322621635))) (.branch 111 (.branch 110 (.leaf 315580645) (.leaf 308698884)) (.branch 112 (.leaf 301972492) (.leaf 295397714)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 288970896) (.leaf 282688485)) (.branch 116 (.leaf 276547022) (.leaf 270543144))) (.branch 119 (.branch 118 (.leaf 264673574) (.leaf 258935124)) (.branch 120 (.leaf 253324691) (.leaf 247839252)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 891).prefactor = (4847016796756901/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 891).cutoff/(generalMeanRows 891).c)).2 =
    (73200807845453/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 891).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 891).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 891).q*(generalMeanRows 891).c/2-2 = (847/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable287.value]
    have hcontinuation : (generalMeanRows 891).q*(generalMeanRows 891).cutoff/2-2 = (40/19:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable284.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 891).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 891

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 891).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 891).criticalRate j.val*(generalMeanRows 891).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 891).c*(generalMeanRows 891).criticalPoint j.val)).2-
      (generalMeanRows 891).J/2-(generalMeanRows 891).error (generalMeanGrid j.val)+
      (generalMeanRows 891).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 891).c)).2-
      (generalMeanRows 891).J/2-(generalMeanRows 891).error 4 := by
  have he : (generalMeanRows 891).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 891) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 891)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0891

/-! Kernel-checked entropy margins for general spectral rectangle 892. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0892
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5185245005) (.branch 2 (.leaf 5014824874) (.leaf 4851851564))) (.branch 5 (.branch 4 (.leaf 4695902416) (.leaf 4546584734)) (.branch 6 (.leaf 4403533159) (.leaf 4266407331)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4134889800) (.leaf 4008684140)) (.branch 10 (.leaf 3887513264) (.leaf 3771117893))) (.branch 13 (.branch 12 (.leaf 3659255179) (.leaf 3551697452)) (.branch 14 (.leaf 3448231083) (.leaf 3348655448))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3252781990) (.branch 17 (.leaf 3160433349) (.leaf 3071442576))) (.branch 20 (.branch 19 (.leaf 2985652413) (.leaf 2902914623)) (.branch 21 (.leaf 2823089383) (.leaf 2746044720)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2671655996) (.leaf 2599805423)) (.branch 25 (.leaf 2530381628) (.leaf 2463279240))) (.branch 28 (.branch 27 (.leaf 2398398511) (.leaf 2335644966)) (.branch 29 (.leaf 2274929077) (.leaf 2216165958)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2159275086) (.branch 32 (.leaf 2104180037) (.leaf 2050808244))) (.branch 35 (.branch 34 (.leaf 1999090767) (.leaf 1948962083)) (.branch 36 (.leaf 1900359885) (.leaf 1853224901)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1807500718) (.leaf 1763133620)) (.branch 40 (.leaf 1720072439) (.leaf 1678268412))) (.branch 43 (.branch 42 (.leaf 1637675046) (.leaf 1598247998)) (.branch 44 (.leaf 1559944954) (.leaf 1522725521))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1486551123) (.branch 47 (.leaf 1451384908) (.leaf 1417191650))) (.branch 50 (.branch 49 (.leaf 1383937672) (.leaf 1351590757)) (.branch 51 (.leaf 1320120081) (.leaf 1289496133)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1259690654) (.leaf 1230676573)) (.branch 55 (.leaf 1202427943) (.leaf 1174919891))) (.branch 58 (.branch 57 (.leaf 1148128560) (.leaf 1122031061)) (.branch 59 (.leaf 1096605426) (.leaf 1071830561))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1047686208) (.branch 62 (.leaf 1024152901) (.leaf 1001211929))) (.branch 65 (.branch 64 (.leaf 978845305) (.leaf 957035725)) (.branch 66 (.leaf 935766540) (.leaf 915021728)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 894785858) (.leaf 875044073)) (.branch 70 (.leaf 855782056) (.leaf 836986008))) (.branch 73 (.branch 72 (.leaf 818642627) (.leaf 800739084)) (.branch 74 (.leaf 783263004) (.leaf 766202442))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 749545870) (.branch 77 (.leaf 733282157) (.leaf 717400549))) (.branch 80 (.branch 79 (.leaf 701890659) (.leaf 686742445)) (.branch 81 (.leaf 671946201) (.leaf 657492542)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 643372387) (.leaf 629576951)) (.branch 85 (.leaf 616097734) (.leaf 602926503))) (.branch 88 (.branch 87 (.leaf 590055288) (.leaf 577476370)) (.branch 89 (.leaf 565182269) (.leaf 553165736)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 541419745) (.branch 92 (.leaf 529937484) (.leaf 518712346))) (.branch 95 (.branch 94 (.leaf 507737923) (.leaf 497007996)) (.branch 96 (.leaf 486516531) (.leaf 476257671)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 466225727) (.leaf 456415176)) (.branch 100 (.leaf 446820655) (.leaf 437436950))) (.branch 103 (.branch 102 (.leaf 428258998) (.leaf 419281876)) (.branch 104 (.leaf 410500798) (.leaf 401911113))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 393508295) (.leaf 385287945)) (.branch 108 (.leaf 377245780) (.leaf 369377636))) (.branch 111 (.branch 110 (.leaf 361679458) (.leaf 354147301)) (.branch 112 (.leaf 346777323) (.leaf 339565785)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332509046) (.leaf 325603557)) (.branch 116 (.leaf 318845864) (.leaf 312232601))) (.branch 119 (.branch 118 (.leaf 305760488) (.leaf 299426329)) (.branch 120 (.leaf 293227009) (.leaf 287159491)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 892).prefactor = (4799871355074377/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 892).cutoff/(generalMeanRows 892).c)).2 =
    (392672286309427/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 892).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 892).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 892).q*(generalMeanRows 892).c/2-2 = (1621/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable288.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 892).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 892

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 892).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 892).criticalRate j.val*(generalMeanRows 892).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 892).c*(generalMeanRows 892).criticalPoint j.val)).2-
      (generalMeanRows 892).J/2-(generalMeanRows 892).error (generalMeanGrid j.val)+
      (generalMeanRows 892).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 892).c)).2-
      (generalMeanRows 892).J/2-(generalMeanRows 892).error 4 := by
  have he : (generalMeanRows 892).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 892) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 892)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0892

/-! Kernel-checked entropy margins for general spectral rectangle 893. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0893
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5095844083) (.branch 2 (.leaf 4916566980) (.leaf 4745262326))) (.branch 5 (.branch 4 (.leaf 4581482045) (.leaf 4424809479)) (.branch 6 (.leaf 4274856649) (.leaf 4131261811)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3993687263) (.leaf 3861817389)) (.branch 10 (.leaf 3735356888) (.leaf 3614029179))) (.branch 13 (.branch 12 (.leaf 3497574961) (.leaf 3385750908)) (.branch 14 (.leaf 3278328479) (.leaf 3175092838))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3075841871) (.branch 17 (.leaf 2980385281) (.leaf 2888543770))) (.branch 20 (.branch 19 (.leaf 2800148275) (.leaf 2715039284)) (.branch 21 (.leaf 2633066188) (.leaf 2554086701)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2477966312) (.leaf 2404577789)) (.branch 25 (.leaf 2333800713) (.leaf 2265521051))) (.branch 28 (.branch 27 (.leaf 2199630760) (.leaf 2136027416)) (.branch 29 (.leaf 2074613875) (.leaf 2015297951)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1957992126) (.branch 32 (.leaf 1902613270) (.leaf 1849082385))) (.branch 35 (.branch 34 (.leaf 1797324367) (.leaf 1747267782)) (.branch 36 (.leaf 1698844656) (.leaf 1651990282)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1606643035) (.leaf 1562744201)) (.branch 40 (.leaf 1520237820) (.leaf 1479070532))) (.branch 43 (.branch 42 (.leaf 1439191437) (.leaf 1400551966)) (.branch 44 (.leaf 1363105753) (.leaf 1326808520))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1291617966) (.branch 47 (.leaf 1257493667) (.leaf 1224396976))) (.branch 50 (.branch 49 (.leaf 1192290933) (.leaf 1161140178)) (.branch 51 (.leaf 1130910872) (.leaf 1101570618)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1073088392) (.leaf 1045434470)) (.branch 55 (.leaf 1018580370) (.leaf 992498788))) (.branch 58 (.branch 57 (.leaf 967163539) (.leaf 942549507)) (.branch 59 (.leaf 918632591) (.leaf 895389660))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 872798501) (.branch 62 (.leaf 850837783) (.leaf 829487009))) (.branch 65 (.branch 64 (.leaf 808726485) (.leaf 788537276)) (.branch 66 (.leaf 768901175) (.leaf 749800669)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 731218908) (.leaf 713139675)) (.branch 70 (.leaf 695547357) (.leaf 678426922))) (.branch 73 (.branch 72 (.leaf 661763887) (.leaf 645544300)) (.branch 74 (.leaf 629754714) (.leaf 614382167))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 599414158) (.branch 77 (.leaf 584838632) (.leaf 570643957))) (.branch 80 (.branch 79 (.leaf 556818909) (.leaf 543352655)) (.branch 81 (.leaf 530234732) (.leaf 517455041)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 505003823) (.leaf 492871651)) (.branch 85 (.leaf 481049413) (.leaf 469528303))) (.branch 88 (.branch 87 (.leaf 458299806) (.leaf 447355687)) (.branch 89 (.leaf 436687981) (.leaf 426288983)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 416151234) (.branch 92 (.leaf 406267518) (.leaf 396630847))) (.branch 95 (.branch 94 (.leaf 387234454) (.leaf 378071789)) (.branch 96 (.leaf 369136501) (.leaf 360422444)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351923655) (.leaf 343634360)) (.branch 100 (.leaf 335548960) (.leaf 327662024))) (.branch 103 (.branch 102 (.leaf 319968288) (.leaf 312462645)) (.branch 104 (.leaf 305140141) (.leaf 297995971))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 291025469) (.leaf 284224108)) (.branch 108 (.leaf 277587495) (.leaf 271111361))) (.branch 111 (.branch 110 (.leaf 264791565) (.leaf 258624082)) (.branch 112 (.leaf 252605004) (.leaf 246730536)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 240996988) (.leaf 235400775)) (.branch 116 (.leaf 229938414) (.leaf 224606519))) (.branch 119 (.branch 118 (.leaf 219401799) (.leaf 214321053)) (.branch 120 (.leaf 209361170) (.leaf 204519122)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 893).prefactor = (1262643420716837/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 893).cutoff/(generalMeanRows 893).c)).2 =
    (345664354990143/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 893).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 893).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 893).q*(generalMeanRows 893).c/2-2 = (1811/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable289.value]
    have hcontinuation : (generalMeanRows 893).q*(generalMeanRows 893).cutoff/2-2 = (40/19:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable284.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 893).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 893

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 893).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 893).criticalRate j.val*(generalMeanRows 893).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 893).c*(generalMeanRows 893).criticalPoint j.val)).2-
      (generalMeanRows 893).J/2-(generalMeanRows 893).error (generalMeanGrid j.val)+
      (generalMeanRows 893).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 893).c)).2-
      (generalMeanRows 893).J/2-(generalMeanRows 893).error 4 := by
  have he : (generalMeanRows 893).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 893) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 893)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0893

/-! Kernel-checked entropy margins for general spectral rectangle 894. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0894
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7392840357) (.branch 2 (.leaf 7185314593) (.leaf 6985883603))) (.branch 5 (.branch 4 (.leaf 6794125892) (.leaf 6609648923)) (.branch 6 (.leaf 6432086505) (.leaf 6261096486)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6096358699) (.leaf 5937573125)) (.branch 10 (.leaf 5784458259) (.leaf 5636749637))) (.branch 13 (.branch 12 (.leaf 5494198517) (.leaf 5356570679)) (.branch 14 (.leaf 5223645352) (.leaf 5095214236))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4971080606) (.branch 17 (.leaf 4851058511) (.leaf 4734972033))) (.branch 20 (.branch 19 (.leaf 4622654608) (.leaf 4513948413)) (.branch 21 (.leaf 4408703794) (.leaf 4306778746)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4208038433) (.leaf 4112354743)) (.branch 25 (.leaf 4019605879) (.leaf 3929675983))) (.branch 28 (.branch 27 (.leaf 3842454779) (.leaf 3757837252)) (.branch 29 (.leaf 3675723345) (.leaf 3596017677)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3518629280) (.branch 32 (.leaf 3443471357) (.leaf 3370461052))) (.branch 35 (.branch 34 (.leaf 3299519237) (.leaf 3230570316)) (.branch 36 (.leaf 3163542036) (.leaf 3098365311)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3034974062) (.leaf 2973305059)) (.branch 40 (.leaf 2913297780) (.leaf 2854894275))) (.branch 43 (.branch 42 (.leaf 2798039036) (.leaf 2742678876)) (.branch 44 (.leaf 2688762821) (.leaf 2636241997))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2585069533) (.branch 47 (.leaf 2535200463) (.leaf 2486591638))) (.branch 50 (.branch 49 (.leaf 2439201642) (.leaf 2392990706)) (.branch 51 (.leaf 2347920641) (.leaf 2303954756)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2261057797) (.leaf 2219195877)) (.branch 55 (.leaf 2178336422) (.leaf 2138448102))) (.branch 58 (.branch 57 (.leaf 2099500785) (.leaf 2061465481)) (.branch 59 (.leaf 2024314291) (.leaf 1988020362))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1952557840) (.branch 62 (.leaf 1917901828) (.leaf 1884028344))) (.branch 65 (.branch 64 (.leaf 1850914285) (.leaf 1818537386)) (.branch 66 (.leaf 1786876189) (.leaf 1755910006)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1725618890) (.leaf 1695983600)) (.branch 70 (.leaf 1666985577) (.leaf 1638606914))) (.branch 73 (.branch 72 (.leaf 1610830328) (.leaf 1583639139)) (.branch 74 (.leaf 1557017240) (.leaf 1530949078))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1505419633) (.branch 77 (.leaf 1480414392) (.leaf 1455919334))) (.branch 80 (.branch 79 (.leaf 1431920907) (.leaf 1408406013)) (.branch 81 (.leaf 1385361988) (.leaf 1362776584)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1340637958) (.leaf 1318934651)) (.branch 85 (.leaf 1297655576) (.leaf 1276790004))) (.branch 88 (.branch 87 (.leaf 1256327549) (.leaf 1236258157)) (.branch 89 (.leaf 1216572092) (.leaf 1197259924)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1178312520) (.branch 92 (.leaf 1159721029) (.leaf 1141476875))) (.branch 95 (.branch 94 (.leaf 1123571748) (.leaf 1105997588)) (.branch 96 (.leaf 1088746582) (.leaf 1071811155)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1055183956) (.leaf 1038857855)) (.branch 100 (.leaf 1022825934) (.leaf 1007081479))) (.branch 103 (.branch 102 (.leaf 991617971) (.leaf 976429085)) (.branch 104 (.leaf 961508674) (.leaf 946850771))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 932449580) (.leaf 918299468)) (.branch 108 (.leaf 904394961) (.leaf 890730742))) (.branch 111 (.branch 110 (.leaf 877301638) (.leaf 864102622)) (.branch 112 (.leaf 851128804) (.leaf 838375429)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 825837871) (.leaf 813511630)) (.branch 116 (.leaf 801392324) (.leaf 789475691))) (.branch 119 (.branch 118 (.leaf 777757581) (.leaf 766233952)) (.branch 120 (.leaf 754900870) (.leaf 743754501)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 894).prefactor = (4802138754079373/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 894).cutoff/(generalMeanRows 894).c)).2 =
    (326732587323669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 894).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 894).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 894).q*(generalMeanRows 894).cutoff/2-2 = (61/40:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable290.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 894).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 894

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 894).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 894).criticalRate j.val*(generalMeanRows 894).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 894).c*(generalMeanRows 894).criticalPoint j.val)).2-
      (generalMeanRows 894).J/2-(generalMeanRows 894).error (generalMeanGrid j.val)+
      (generalMeanRows 894).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 894).c)).2-
      (generalMeanRows 894).J/2-(generalMeanRows 894).error 4 := by
  have he : (generalMeanRows 894).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 894) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 894)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0894

/-! Kernel-checked entropy margins for general spectral rectangle 895. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0895
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6850608711) (.branch 2 (.leaf 6635085052) (.leaf 6428153395))) (.branch 5 (.branch 4 (.leaf 6229369868) (.leaf 6038320910)) (.branch 6 (.leaf 5854620549) (.leaf 5677907980)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5507845423) (.leaf 5344116204)) (.branch 10 (.leaf 5186423041) (.leaf 5034486511))) (.branch 13 (.branch 12 (.leaf 4888043662) (.leaf 4746846771)) (.branch 14 (.leaf 4610662208) (.leaf 4479269421))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4352460002) (.branch 17 (.leaf 4230036842) (.leaf 4111813358))) (.branch 20 (.branch 19 (.leaf 3997612789) (.leaf 3887267548)) (.branch 21 (.leaf 3780618626) (.leaf 3677515051)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3577813382) (.leaf 3481377247)) (.branch 25 (.leaf 3388076914) (.leaf 3297788894))) (.branch 28 (.branch 27 (.leaf 3210395576) (.leaf 3125784885)) (.branch 29 (.leaf 3043849966) (.leaf 2964488891)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2887604381) (.branch 32 (.leaf 2813103557) (.leaf 2740897695))) (.branch 35 (.branch 34 (.leaf 2670902008) (.leaf 2603035434)) (.branch 36 (.leaf 2537220444) (.leaf 2473382858)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2411451674) (.leaf 2351358906)) (.branch 40 (.leaf 2293039432) (.leaf 2236430855))) (.branch 43 (.branch 42 (.leaf 2181473367) (.leaf 2128109622)) (.branch 44 (.leaf 2076284620) (.leaf 2025945593))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1977041900) (.branch 47 (.leaf 1929524925) (.leaf 1883347986))) (.branch 50 (.branch 49 (.leaf 1838466245) (.leaf 1794836621)) (.branch 51 (.leaf 1752417712) (.leaf 1711169720)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1671054378) (.leaf 1632034883)) (.branch 55 (.leaf 1594075829) (.leaf 1557143149))) (.branch 58 (.branch 57 (.leaf 1521204056) (.leaf 1486226984)) (.branch 59 (.leaf 1452181541) (.leaf 1419038457))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1386769535) (.branch 62 (.leaf 1355347605) (.leaf 1324746488))) (.branch 65 (.branch 64 (.leaf 1294940943) (.leaf 1265906641)) (.branch 66 (.leaf 1237620118) (.leaf 1210058744)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1183200688) (.leaf 1157024885)) (.branch 70 (.leaf 1131511009) (.leaf 1106639438))) (.branch 73 (.branch 72 (.leaf 1082391229) (.leaf 1058748092)) (.branch 74 (.leaf 1035692362) (.leaf 1013206976))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 991275450) (.branch 77 (.leaf 969881854) (.leaf 949010796))) (.branch 80 (.branch 79 (.leaf 928647393) (.leaf 908777261)) (.branch 81 (.leaf 889386488) (.leaf 870461622)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 851989651) (.leaf 833957986)) (.branch 85 (.leaf 816354447) (.leaf 799167246))) (.branch 88 (.branch 87 (.leaf 782384975) (.leaf 765996589)) (.branch 89 (.leaf 749991396) (.leaf 734359041)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 719089495) (.branch 92 (.leaf 704173045) (.leaf 689600280))) (.branch 95 (.branch 94 (.leaf 675362082) (.leaf 661449614)) (.branch 96 (.leaf 647854311) (.leaf 634567872)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 621582246) (.leaf 608889630)) (.branch 100 (.leaf 596482453) (.leaf 584353375))) (.branch 103 (.branch 102 (.leaf 572495272) (.leaf 560901236)) (.branch 104 (.leaf 549564561) (.leaf 538478741))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 527637458) (.leaf 517034583)) (.branch 108 (.leaf 506664162) (.leaf 496520415))) (.branch 111 (.branch 110 (.leaf 486597729) (.leaf 476890652)) (.branch 112 (.leaf 467393887) (.leaf 458102288)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 449010856) (.leaf 440114732)) (.branch 116 (.leaf 431409194) (.leaf 422889652))) (.branch 119 (.branch 118 (.leaf 414551642) (.leaf 406390826)) (.branch 120 (.leaf 398402985) (.leaf 390584016)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 895).prefactor = (1261118671186149/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 895).cutoff/(generalMeanRows 895).c)).2 =
    (64582465109817/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 895).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 895).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 895).q*(generalMeanRows 895).c/2-2 = (289/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable093.value]
    have hcontinuation : (generalMeanRows 895).q*(generalMeanRows 895).cutoff/2-2 = (61/40:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable290.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 895).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 895

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 895).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 895).criticalRate j.val*(generalMeanRows 895).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 895).c*(generalMeanRows 895).criticalPoint j.val)).2-
      (generalMeanRows 895).J/2-(generalMeanRows 895).error (generalMeanGrid j.val)+
      (generalMeanRows 895).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 895).c)).2-
      (generalMeanRows 895).J/2-(generalMeanRows 895).error 4 := by
  have he : (generalMeanRows 895).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 895) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 895)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0895

/-! Kernel-checked entropy margins for general spectral rectangle 896. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0896
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6728311106) (.branch 2 (.leaf 6520999017) (.leaf 6321993782))) (.branch 5 (.branch 4 (.leaf 6130861699) (.leaf 5947198746)) (.branch 6 (.leaf 5770627926) (.leaf 5600796910)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5437375950) (.leaf 5280056001)) (.branch 10 (.leaf 5128547054) (.leaf 4982576630))) (.branch 13 (.branch 12 (.leaf 4841888423) (.leaf 4706241087)) (.branch 14 (.leaf 4575407120) (.leaf 4449171869))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4327332612) (.branch 17 (.leaf 4209697732) (.leaf 4096085952))) (.branch 20 (.branch 19 (.leaf 3986325647) (.leaf 3880254203)) (.branch 21 (.leaf 3777717434) (.leaf 3678569047)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3582670144) (.leaf 3489888763)) (.branch 25 (.leaf 3400099463) (.leaf 3313182926))) (.branch 28 (.branch 27 (.leaf 3229025598) (.leaf 3147519352)) (.branch 29 (.leaf 3068561178) (.leaf 2992052889)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2917900853) (.branch 32 (.leaf 2846015740) (.leaf 2776312285))) (.branch 35 (.branch 34 (.leaf 2708709072) (.leaf 2643128324)) (.branch 36 (.leaf 2579495712) (.leaf 2517740176)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2457793751) (.leaf 2399591415)) (.branch 40 (.leaf 2343070933) (.leaf 2288172722))) (.branch 43 (.branch 42 (.leaf 2234839716) (.leaf 2183017242)) (.branch 44 (.leaf 2132652901) (.leaf 2083696464))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2036099760) (.branch 47 (.leaf 1989816583) (.leaf 1944802595))) (.branch 50 (.branch 49 (.leaf 1901015242) (.leaf 1858413670)) (.branch 51 (.leaf 1816958644) (.leaf 1776612474)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1737338949) (.leaf 1699103265)) (.branch 55 (.leaf 1661871964) (.leaf 1625612872))) (.branch 58 (.branch 57 (.leaf 1590295046) (.leaf 1555888715)) (.branch 59 (.leaf 1522365233) (.leaf 1489697026))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1457857549) (.branch 62 (.leaf 1426821240) (.leaf 1396563479))) (.branch 65 (.branch 64 (.leaf 1367060547) (.leaf 1338289588)) (.branch 66 (.leaf 1310228573) (.leaf 1282856267)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1256152194) (.leaf 1230096607)) (.branch 70 (.leaf 1204670455) (.leaf 1179855361))) (.branch 73 (.branch 72 (.leaf 1155633587) (.leaf 1131988014)) (.branch 74 (.leaf 1108902115) (.leaf 1086359930))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1064346047) (.branch 77 (.leaf 1042845575) (.leaf 1021844130))) (.branch 80 (.branch 79 (.leaf 1001327809) (.leaf 981283175)) (.branch 81 (.leaf 961697239) (.leaf 942557440)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 923851632) (.leaf 905568063)) (.branch 85 (.leaf 887695368) (.leaf 870222545))) (.branch 88 (.branch 87 (.leaf 853138950) (.leaf 836434278)) (.branch 89 (.leaf 820098552) (.leaf 804122110)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 788495595) (.branch 92 (.leaf 773209944) (.leaf 758256374))) (.branch 95 (.branch 94 (.leaf 743626376) (.leaf 729311701)) (.branch 96 (.leaf 715304356) (.leaf 701596587)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 688180879) (.leaf 675049942)) (.branch 100 (.leaf 662196703) (.leaf 649614301))) (.branch 103 (.branch 102 (.leaf 637296080) (.leaf 625235577)) (.branch 104 (.leaf 613426522) (.leaf 601862825))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 590538575) (.leaf 579448029)) (.branch 108 (.leaf 568585610) (.leaf 557945902))) (.branch 111 (.branch 110 (.leaf 547523640) (.leaf 537313709)) (.branch 112 (.leaf 527311138) (.leaf 517511093)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 507908877) (.leaf 498499921)) (.branch 116 (.leaf 489279782) (.leaf 480244139))) (.branch 119 (.branch 118 (.leaf 471388788) (.leaf 462709638)) (.branch 120 (.leaf 454202710) (.leaf 445864130)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 896).prefactor = (1233251389090051/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 896).cutoff/(generalMeanRows 896).c)).2 =
    (29092135582301/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 896).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 896).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 896).q*(generalMeanRows 896).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 896).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 896

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 896).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 896).criticalRate j.val*(generalMeanRows 896).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 896).c*(generalMeanRows 896).criticalPoint j.val)).2-
      (generalMeanRows 896).J/2-(generalMeanRows 896).error (generalMeanGrid j.val)+
      (generalMeanRows 896).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 896).c)).2-
      (generalMeanRows 896).J/2-(generalMeanRows 896).error 4 := by
  have he : (generalMeanRows 896).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 896) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 896)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0896

/-! Kernel-checked entropy margins for general spectral rectangle 897. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0897
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6557158493) (.branch 2 (.leaf 6358921194) (.leaf 6168680746))) (.branch 5 (.branch 4 (.leaf 5986014564) (.leaf 5810529074)) (.branch 6 (.leaf 5641857127) (.leaf 5479655715)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5323603929) (.leaf 5173401134)) (.branch 10 (.leaf 5028765342) (.leaf 4889431738))) (.branch 13 (.branch 12 (.leaf 4755151360) (.leaf 4625689904)) (.branch 14 (.leaf 4500826642) (.leaf 4380353435))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4264073847) (.branch 17 (.leaf 4151802321) (.leaf 4043363439))) (.branch 20 (.branch 19 (.leaf 3938591242) (.leaf 3837328598)) (.branch 21 (.leaf 3739426634) (.leaf 3644744205)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3553147408) (.leaf 3464509129)) (.branch 25 (.leaf 3378708631) (.leaf 3295631169))) (.branch 28 (.branch 27 (.leaf 3215167629) (.leaf 3137214202)) (.branch 29 (.leaf 3061672076) (.leaf 2988447146)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2917449749) (.branch 32 (.leaf 2848594418) (.leaf 2781799647))) (.branch 35 (.branch 34 (.leaf 2716987674) (.leaf 2654084281)) (.branch 36 (.leaf 2593018602) (.leaf 2533722946)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2476132629) (.leaf 2420185819)) (.branch 40 (.leaf 2365823389) (.leaf 2312988778))) (.branch 43 (.branch 42 (.leaf 2261627863) (.leaf 2211688832)) (.branch 44 (.leaf 2163122076) (.leaf 2115880074))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2069917293) (.branch 47 (.leaf 2025190094) (.leaf 1981656636))) (.branch 50 (.branch 49 (.leaf 1939276793) (.leaf 1898012074)) (.branch 51 (.leaf 1857825539) (.leaf 1818681737)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1780546626) (.leaf 1743387515)) (.branch 55 (.leaf 1707173001) (.leaf 1671872907))) (.branch 58 (.branch 57 (.leaf 1637458229) (.leaf 1603901084)) (.branch 59 (.leaf 1571174657) (.leaf 1539253157))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1508111769) (.branch 62 (.leaf 1477726611) (.leaf 1448074698))) (.branch 65 (.branch 64 (.leaf 1419133894) (.leaf 1390882886)) (.branch 66 (.leaf 1363301141) (.leaf 1336368874)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1310067019) (.leaf 1284377197)) (.branch 70 (.leaf 1259281688) (.leaf 1234763399))) (.branch 73 (.branch 72 (.leaf 1210805847) (.leaf 1187393124)) (.branch 74 (.leaf 1164509880) (.leaf 1142141298))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1120273071) (.branch 77 (.leaf 1098891383) (.leaf 1077982891))) (.branch 80 (.branch 79 (.leaf 1057534701) (.leaf 1037534354)) (.branch 81 (.leaf 1017969810) (.leaf 998829426)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 980101946) (.leaf 961776483)) (.branch 85 (.leaf 943842506) (.leaf 926289823))) (.branch 88 (.branch 87 (.leaf 909108573) (.leaf 892289211)) (.branch 89 (.leaf 875822495) (.leaf 859699474)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 843911480) (.branch 92 (.leaf 828450117) (.leaf 813307247))) (.branch 95 (.branch 94 (.leaf 798474984) (.leaf 783945684)) (.branch 96 (.leaf 769711936) (.leaf 755766554)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 742102566) (.leaf 728713210)) (.branch 100 (.leaf 715591926) (.leaf 702732345))) (.branch 103 (.branch 102 (.leaf 690128286) (.leaf 677773749)) (.branch 104 (.leaf 665662908) (.leaf 653790102))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 642149835) (.leaf 630736766)) (.branch 108 (.leaf 619545705) (.leaf 608571608))) (.branch 111 (.branch 110 (.leaf 597809570) (.leaf 587254825)) (.branch 112 (.leaf 576902737) (.leaf 566748795)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 556788613) (.leaf 547017925)) (.branch 116 (.leaf 537432575) (.leaf 528028523))) (.branch 119 (.branch 118 (.leaf 518801833) (.leaf 509748674)) (.branch 120 (.leaf 500865316) (.leaf 492148125)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 897).prefactor = (961864045992719/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 897).cutoff/(generalMeanRows 897).c)).2 =
    (32126085890703/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 897).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 897).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 897).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 897

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 897).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 897).criticalRate j.val*(generalMeanRows 897).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 897).c*(generalMeanRows 897).criticalPoint j.val)).2-
      (generalMeanRows 897).J/2-(generalMeanRows 897).error (generalMeanGrid j.val)+
      (generalMeanRows 897).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 897).c)).2-
      (generalMeanRows 897).J/2-(generalMeanRows 897).error 4 := by
  have he : (generalMeanRows 897).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 897) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 897)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0897

/-! Kernel-checked entropy margins for general spectral rectangle 898. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0898
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6343712093) (.branch 2 (.leaf 6155121120) (.leaf 5974197768))) (.branch 5 (.branch 4 (.leaf 5800531410) (.leaf 5633739728)) (.branch 6 (.leaf 5473466212) (.leaf 5319377932)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5171163553) (.leaf 5028531562)) (.branch 10 (.leaf 4891208672) (.leaf 4758938394))) (.branch 13 (.branch 12 (.leaf 4631479745) (.leaf 4508606077)) (.branch 14 (.leaf 4390104020) (.leaf 4275772521))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4165421968) (.branch 17 (.leaf 4058873390) (.leaf 3955957729))) (.branch 20 (.branch 19 (.leaf 3856515169) (.leaf 3760394523)) (.branch 21 (.leaf 3667452670) (.leaf 3577554036)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3490570114) (.leaf 3406379024)) (.branch 25 (.leaf 3324865100) (.leaf 3245918519))) (.branch 28 (.branch 27 (.leaf 3169434945) (.leaf 3095315204)) (.branch 29 (.leaf 3023464983) (.leaf 2953794546)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2886218477) (.branch 32 (.leaf 2820655428) (.leaf 2757027898))) (.branch 35 (.branch 34 (.leaf 2695262017) (.leaf 2635287343)) (.branch 36 (.leaf 2577036683) (.leaf 2520445912)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2465453814) (.leaf 2412001923)) (.branch 40 (.leaf 2360034386) (.leaf 2309497819))) (.branch 43 (.branch 42 (.leaf 2260341187) (.leaf 2212515681)) (.branch 44 (.leaf 2165974603) (.leaf 2120673266))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2076568887) (.branch 47 (.leaf 2033620496) (.leaf 1991788848))) (.branch 50 (.branch 49 (.leaf 1951036337) (.leaf 1911326916)) (.branch 51 (.leaf 1872626022) (.leaf 1834900510)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1798118576) (.leaf 1762249704)) (.branch 55 (.leaf 1727264598) (.leaf 1693135130))) (.branch 58 (.branch 57 (.leaf 1659834283) (.leaf 1627336100)) (.branch 59 (.leaf 1595615639) (.leaf 1564648923))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1534412896) (.branch 62 (.leaf 1504885386) (.leaf 1476045061))) (.branch 65 (.branch 64 (.leaf 1447871394) (.leaf 1420344627)) (.branch 66 (.leaf 1393445738) (.leaf 1367156407)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1341458986) (.leaf 1316336471)) (.branch 70 (.leaf 1291772476) (.leaf 1267751200))) (.branch 73 (.branch 72 (.leaf 1244257411) (.leaf 1221276415)) (.branch 74 (.leaf 1198794036) (.leaf 1176796595))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1155270888) (.branch 77 (.leaf 1134204169) (.leaf 1113584125))) (.branch 80 (.branch 79 (.leaf 1093398867) (.leaf 1073636903)) (.branch 81 (.leaf 1054287132) (.leaf 1035338821)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1016781591) (.leaf 998605407)) (.branch 85 (.leaf 980800561) (.leaf 963357659))) (.branch 88 (.branch 87 (.leaf 946267611) (.leaf 929521616)) (.branch 89 (.leaf 913111154) (.leaf 897027972)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 881264078) (.branch 92 (.leaf 865811726) (.leaf 850663410))) (.branch 95 (.branch 94 (.leaf 835811854) (.leaf 821250004)) (.branch 96 (.leaf 806971018) (.leaf 792968261)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 779235293) (.leaf 765765868)) (.branch 100 (.leaf 752553919) (.leaf 739593559))) (.branch 103 (.branch 102 (.leaf 726879072) (.leaf 714404904)) (.branch 104 (.leaf 702165660) (.leaf 690156099))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 678371126) (.leaf 666805790)) (.branch 108 (.leaf 655455276) (.leaf 644314902))) (.branch 111 (.branch 110 (.leaf 633380113) (.leaf 622646480)) (.branch 112 (.leaf 612109692) (.leaf 601765552)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 591609978) (.leaf 581638993)) (.branch 116 (.leaf 571848725) (.leaf 562235402))) (.branch 119 (.branch 118 (.leaf 552795352) (.leaf 543524996)) (.branch 120 (.leaf 534420844) (.leaf 525479498)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 898).prefactor = (73070009182951/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 898).cutoff/(generalMeanRows 898).c)).2 =
    (349648018974057/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 898).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 898).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 898).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 898

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 898).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 898).criticalRate j.val*(generalMeanRows 898).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 898).c*(generalMeanRows 898).criticalPoint j.val)).2-
      (generalMeanRows 898).J/2-(generalMeanRows 898).error (generalMeanGrid j.val)+
      (generalMeanRows 898).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 898).c)).2-
      (generalMeanRows 898).J/2-(generalMeanRows 898).error 4 := by
  have he : (generalMeanRows 898).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 898) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 898)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0898

/-! Kernel-checked entropy margins for general spectral rectangle 899. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0899
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5963096729) (.branch 2 (.leaf 5777091743) (.leaf 5598766129))) (.branch 5 (.branch 4 (.leaf 5427707530) (.leaf 5263532000)) (.branch 6 (.leaf 5105881498) (.leaf 4954421658)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4808839802) (.leaf 4668843165)) (.branch 10 (.leaf 4534157293) (.leaf 4404524610))) (.branch 13 (.branch 12 (.leaf 4279703125) (.leaf 4159465251)) (.branch 14 (.leaf 4043596752) (.leaf 3931895772))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3824171953) (.branch 17 (.leaf 3720245640) (.leaf 3619947137))) (.branch 20 (.branch 19 (.leaf 3523116045) (.leaf 3429600635)) (.branch 21 (.leaf 3339257290) (.leaf 3251949976)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3167549764) (.leaf 3085934384)) (.branch 25 (.leaf 3006987815) (.leaf 2930599903))) (.branch 28 (.branch 27 (.leaf 2856666011) (.leaf 2785086684)) (.branch 29 (.leaf 2715767356) (.leaf 2648618055)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2583553147) (.branch 32 (.leaf 2520491087) (.leaf 2459354190))) (.branch 35 (.branch 34 (.leaf 2400068416) (.leaf 2342563170)) (.branch 36 (.leaf 2286771114) (.leaf 2232627993)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2180072467) (.leaf 2129045959)) (.branch 40 (.leaf 2079492510) (.leaf 2031358640))) (.branch 43 (.branch 42 (.leaf 1984593225) (.leaf 1939147371)) (.branch 44 (.leaf 1894974305) (.leaf 1852029265))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1810269401) (.branch 47 (.leaf 1769653681) (.leaf 1730142800))) (.branch 50 (.branch 49 (.leaf 1691699094) (.leaf 1654286466)) (.branch 51 (.leaf 1617870303) (.leaf 1582417411)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1547895945) (.leaf 1514275343)) (.branch 55 (.leaf 1481526271) (.leaf 1449620561))) (.branch 58 (.branch 57 (.leaf 1418531161) (.leaf 1388232079)) (.branch 59 (.leaf 1358698338) (.leaf 1329905930))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1301831768) (.branch 62 (.leaf 1274453651) (.leaf 1247750218))) (.branch 65 (.branch 64 (.leaf 1221700916) (.leaf 1196285960)) (.branch 66 (.leaf 1171486304) (.leaf 1147283602)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1123660186) (.leaf 1100599029)) (.branch 70 (.leaf 1078083723) (.leaf 1056098450))) (.branch 73 (.branch 72 (.leaf 1034627956) (.leaf 1013657532)) (.branch 74 (.leaf 993172984) (.leaf 973160618))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 953607215) (.branch 77 (.leaf 934500014) (.leaf 915826692))) (.branch 80 (.branch 79 (.leaf 897575346) (.leaf 879734477)) (.branch 81 (.leaf 862292972) (.leaf 845240089)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 828565446) (.leaf 812258999)) (.branch 85 (.leaf 796311036) (.leaf 780712160))) (.branch 88 (.branch 87 (.leaf 765453278) (.leaf 750525589)) (.branch 89 (.leaf 735920573) (.leaf 721629978)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 707645815) (.branch 92 (.leaf 693960341) (.leaf 680566057))) (.branch 95 (.branch 94 (.leaf 667455693) (.leaf 654622202)) (.branch 96 (.leaf 642058752) (.leaf 629758717)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 617715670) (.leaf 605923377)) (.branch 100 (.leaf 594375787) (.leaf 583067028))) (.branch 103 (.branch 102 (.leaf 571991400) (.leaf 561143368)) (.branch 104 (.leaf 550517557) (.leaf 540108745))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 529911862) (.leaf 519921978)) (.branch 108 (.leaf 510134304) (.leaf 500544183))) (.branch 111 (.branch 110 (.leaf 491147089) (.leaf 481938620)) (.branch 112 (.leaf 472914495) (.leaf 464070549)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 455402730) (.leaf 446907097)) (.branch 116 (.leaf 438579811) (.leaf 430417137))) (.branch 119 (.branch 118 (.leaf 422415439) (.leaf 414571175)) (.branch 120 (.leaf 406880897) (.leaf 399341245)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 899).prefactor = (2345913484630603/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 899).cutoff/(generalMeanRows 899).c)).2 =
    (166785034503923/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 899).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 899).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 899).q*(generalMeanRows 899).c/2-2 = (5663/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable205.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 899).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 899

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 899).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 899).criticalRate j.val*(generalMeanRows 899).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 899).c*(generalMeanRows 899).criticalPoint j.val)).2-
      (generalMeanRows 899).J/2-(generalMeanRows 899).error (generalMeanGrid j.val)+
      (generalMeanRows 899).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 899).c)).2-
      (generalMeanRows 899).J/2-(generalMeanRows 899).error 4 := by
  have he : (generalMeanRows 899).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 899) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 899)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0899

/-! Kernel-checked entropy margins for general spectral rectangle 900. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0900
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5558544614) (.branch 2 (.leaf 5376123707) (.leaf 5201377025))) (.branch 5 (.branch 4 (.leaf 5033890921) (.leaf 4873280225)) (.branch 6 (.leaf 4719185734) (.leaf 4571271992)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4429225297) (.leaf 4292751921)) (.branch 10 (.leaf 4161576519) (.leaf 4035440683))) (.branch 13 (.branch 12 (.leaf 3914101647) (.leaf 3797331112)) (.branch 14 (.leaf 3684914183) (.leaf 3576648392))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3472342825) (.branch 17 (.leaf 3371817312) (.leaf 3274901688))) (.branch 20 (.branch 19 (.leaf 3181435123) (.leaf 3091265499)) (.branch 21 (.leaf 3004248842) (.leaf 2920248795)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2839136137) (.leaf 2760788335)) (.branch 25 (.leaf 2685089131) (.leaf 2611928159))) (.branch 28 (.branch 27 (.leaf 2541200592) (.leaf 2472806809)) (.branch 29 (.leaf 2406652093) (.leaf 2342646342)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2280703809) (.branch 32 (.leaf 2220742850) (.leaf 2162685696))) (.branch 35 (.branch 34 (.leaf 2106458235) (.leaf 2051989813)) (.branch 36 (.leaf 1999213044) (.leaf 1948063633)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1898480214) (.leaf 1850404187)) (.branch 40 (.leaf 1803779582) (.leaf 1758552913))) (.branch 43 (.branch 42 (.leaf 1714673058) (.leaf 1672091130)) (.branch 44 (.leaf 1630760369) (.leaf 1590636031))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1551675289) (.branch 47 (.leaf 1513837138) (.leaf 1477082303))) (.branch 50 (.branch 49 (.leaf 1441373157) (.leaf 1406673639)) (.branch 51 (.leaf 1372949178) (.leaf 1340166623)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1308294176) (.leaf 1277301326)) (.branch 55 (.leaf 1247158788) (.leaf 1217838450))) (.branch 58 (.branch 57 (.leaf 1189313313) (.leaf 1161557443)) (.branch 59 (.leaf 1134545924) (.leaf 1108254805))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1082661066) (.branch 62 (.leaf 1057742566) (.leaf 1033478011))) (.branch 65 (.branch 64 (.leaf 1009846914) (.leaf 986829558)) (.branch 66 (.leaf 964406966) (.leaf 942560863)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 921273651) (.leaf 900528377)) (.branch 70 (.leaf 880308706) (.leaf 860598894))) (.branch 73 (.branch 72 (.leaf 841383766) (.leaf 822648685)) (.branch 74 (.leaf 804379539) (.leaf 786562710))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 769185061) (.branch 77 (.leaf 752233911) (.leaf 735697019))) (.branch 80 (.branch 79 (.leaf 719562564) (.leaf 703819131)) (.branch 81 (.leaf 688455692) (.leaf 673461591)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 658826531) (.leaf 644540557)) (.branch 85 (.leaf 630594045) (.leaf 616977687))) (.branch 88 (.branch 87 (.leaf 603682480) (.leaf 590699715)) (.branch 89 (.leaf 578020962) (.leaf 565638064)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 553543124) (.branch 92 (.leaf 541728495) (.leaf 530186772))) (.branch 95 (.branch 94 (.leaf 518910782) (.leaf 507893574)) (.branch 96 (.leaf 497128415) (.leaf 486608777)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 476328332) (.leaf 466280947)) (.branch 100 (.leaf 456460672) (.leaf 446861735))) (.branch 103 (.branch 102 (.leaf 437478539) (.leaf 428305653)) (.branch 104 (.leaf 419337805) (.leaf 410569878))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 401996905) (.leaf 393614064)) (.branch 108 (.leaf 385416671) (.leaf 377400176))) (.branch 111 (.branch 110 (.leaf 369560161) (.leaf 361892331)) (.branch 112 (.leaf 354392514) (.leaf 347056654)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 339880809) (.leaf 332861146)) (.branch 116 (.leaf 325993938) (.leaf 319275560))) (.branch 119 (.branch 118 (.leaf 312702488) (.leaf 306271292)) (.branch 120 (.leaf 299978634) (.leaf 293821268)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 900).prefactor = (939538897218537/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 900).cutoff/(generalMeanRows 900).c)).2 =
    (616833803603/1953125000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 900).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 900).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 900).q*(generalMeanRows 900).c/2-2 = (197/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable218.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 900).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 900

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 900).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 900).criticalRate j.val*(generalMeanRows 900).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 900).c*(generalMeanRows 900).criticalPoint j.val)).2-
      (generalMeanRows 900).J/2-(generalMeanRows 900).error (generalMeanGrid j.val)+
      (generalMeanRows 900).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 900).c)).2-
      (generalMeanRows 900).J/2-(generalMeanRows 900).error 4 := by
  have he : (generalMeanRows 900).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 900) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 900)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0900

/-! Kernel-checked entropy margins for general spectral rectangle 901. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0901
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5587305000) (.branch 2 (.leaf 5414211374) (.leaf 5248367998))) (.branch 5 (.branch 4 (.leaf 5089377300) (.leaf 4936869366)) (.branch 6 (.leaf 4790499515) (.leaf 4649946138)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4514908767) (.leaf 4385106341)) (.branch 10 (.leaf 4260275659) (.leaf 4140169972))) (.branch 13 (.branch 12 (.leaf 4024557721) (.leaf 3913221390)) (.branch 14 (.leaf 3805956470) (.leaf 3702570508))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3602882247) (.branch 17 (.leaf 3506720843) (.leaf 3413925139))) (.branch 20 (.branch 19 (.leaf 3324343007) (.leaf 3237830745)) (.branch 21 (.leaf 3154252517) (.leaf 3073479839)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2995391111) (.leaf 2919871173)) (.branch 25 (.leaf 2846810908) (.leaf 2776106863))) (.branch 28 (.branch 27 (.leaf 2707660904) (.leaf 2641379894)) (.branch 29 (.leaf 2577175393) (.leaf 2514963382)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2454664004) (.branch 32 (.leaf 2396201319) (.leaf 2339503084))) (.branch 35 (.branch 34 (.leaf 2284500539) (.leaf 2231128212)) (.branch 36 (.leaf 2179323737) (.leaf 2129027680)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2080183380) (.leaf 2032736796)) (.branch 40 (.leaf 1986636368) (.leaf 1941832882))) (.branch 43 (.branch 42 (.leaf 1898279349) (.leaf 1855930883)) (.branch 44 (.leaf 1814744594) (.leaf 1774679487))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1735696357) (.branch 47 (.leaf 1697757706) (.leaf 1660827649))) (.branch 50 (.branch 49 (.leaf 1624871840) (.leaf 1589857386)) (.branch 51 (.leaf 1555752785) (.leaf 1522527848)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1490153641) (.leaf 1458602421)) (.branch 55 (.leaf 1427847577) (.leaf 1397863580))) (.branch 58 (.branch 57 (.leaf 1368625928) (.leaf 1340111096)) (.branch 59 (.leaf 1312296494) (.leaf 1285160419))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1258682016) (.branch 62 (.leaf 1232841241) (.leaf 1207618816))) (.branch 65 (.branch 64 (.leaf 1182996202) (.leaf 1158955561)) (.branch 66 (.leaf 1135479727) (.leaf 1112552171)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1090156981) (.leaf 1068278824)) (.branch 70 (.leaf 1046902929) (.leaf 1026015058))) (.branch 73 (.branch 72 (.leaf 1005601486) (.leaf 985648974)) (.branch 74 (.leaf 966144754) (.leaf 947076501))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 928432324) (.branch 77 (.leaf 910200740) (.leaf 892370659))) (.branch 80 (.branch 79 (.leaf 874931369) (.leaf 857872518)) (.branch 81 (.leaf 841184102) (.leaf 824856449)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 808880205) (.leaf 793246320)) (.branch 85 (.leaf 777946042) (.leaf 762970897))) (.branch 88 (.branch 87 (.leaf 748312682) (.leaf 733963455)) (.branch 89 (.leaf 719915524) (.leaf 706161436)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 692693970) (.branch 92 (.leaf 679506124) (.leaf 666591112))) (.branch 95 (.branch 94 (.leaf 653942354) (.leaf 641553464)) (.branch 96 (.leaf 629418250) (.leaf 617530701)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 605884984) (.leaf 594475433)) (.branch 100 (.leaf 583296548) (.leaf 572342987))) (.branch 103 (.branch 102 (.leaf 561609559) (.leaf 551091221)) (.branch 104 (.leaf 540783069) (.leaf 530680339))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 520778396) (.leaf 511072735)) (.branch 108 (.leaf 501558970) (.leaf 492232837))) (.branch 111 (.branch 110 (.leaf 483090185) (.leaf 474126976)) (.branch 112 (.leaf 465339274) (.leaf 456723253)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 448275183) (.leaf 439991431)) (.branch 116 (.leaf 431868459) (.leaf 423902820))) (.branch 119 (.branch 118 (.leaf 416091153) (.leaf 408430183)) (.branch 120 (.leaf 400916718) (.leaf 393547644)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 901).prefactor = (2267908576396939/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 901).cutoff/(generalMeanRows 901).c)).2 =
    (184146158515231/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 901).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 901).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 901).q*(generalMeanRows 901).c/2-2 = (71/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable291.value]
    have hcontinuation : (generalMeanRows 901).q*(generalMeanRows 901).cutoff/2-2 = (23/12:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable028.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 901).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 901

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 901).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 901).criticalRate j.val*(generalMeanRows 901).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 901).c*(generalMeanRows 901).criticalPoint j.val)).2-
      (generalMeanRows 901).J/2-(generalMeanRows 901).error (generalMeanGrid j.val)+
      (generalMeanRows 901).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 901).c)).2-
      (generalMeanRows 901).J/2-(generalMeanRows 901).error 4 := by
  have he : (generalMeanRows 901).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 901) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 901)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0901

/-! Kernel-checked entropy margins for general spectral rectangle 902. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0902
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5323006858) (.branch 2 (.leaf 5153392603) (.leaf 4990968788))) (.branch 5 (.branch 4 (.leaf 4835339020) (.leaf 4686134535)) (.branch 6 (.leaf 4543011786) (.leaf 4405650278)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4273750643) (.leaf 4147032917)) (.branch 10 (.leaf 4025234976) (.leaf 3908111147))) (.branch 13 (.branch 12 (.leaf 3795430935) (.leaf 3686977882)) (.branch 14 (.leaf 3582548525) (.leaf 3481951449))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3385006425) (.branch 17 (.leaf 3291543624) (.leaf 3201402892))) (.branch 20 (.branch 19 (.leaf 3114433093) (.leaf 3030491502)) (.branch 21 (.leaf 2949443245) (.leaf 2871160786)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2795523454) (.leaf 2722417006)) (.branch 25 (.leaf 2651733221) (.leaf 2583369525))) (.branch 28 (.branch 27 (.leaf 2517228645) (.leaf 2453218287)) (.branch 29 (.leaf 2391250835) (.leaf 2331243076)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2273115936) (.branch 32 (.leaf 2216794243) (.leaf 2162206499))) (.branch 35 (.branch 34 (.leaf 2109284672) (.leaf 2057963998)) (.branch 36 (.leaf 2008182800) (.leaf 1959882312)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1913006523) (.leaf 1867502025)) (.branch 40 (.leaf 1823317868) (.leaf 1780405435))) (.branch 43 (.branch 42 (.leaf 1738718310) (.leaf 1698212167)) (.branch 44 (.leaf 1658844658) (.leaf 1620575309))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1583365423) (.branch 47 (.leaf 1547177992) (.leaf 1511977606))) (.branch 50 (.branch 49 (.leaf 1477730375) (.leaf 1444403853)) (.branch 51 (.leaf 1411966962) (.leaf 1380389929)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1349644219) (.leaf 1319702474)) (.branch 55 (.leaf 1290538458) (.leaf 1262126999))) (.branch 58 (.branch 57 (.leaf 1234443942) (.leaf 1207466098)) (.branch 59 (.leaf 1181171199) (.leaf 1155537856))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1130545513) (.branch 62 (.leaf 1106174415) (.leaf 1082405567))) (.branch 65 (.branch 64 (.leaf 1059220698) (.leaf 1036602232)) (.branch 66 (.leaf 1014533252) (.leaf 992997475)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 971979220) (.leaf 951463382)) (.branch 70 (.leaf 931435408) (.leaf 911881271))) (.branch 73 (.branch 72 (.leaf 892787448) (.leaf 874140898)) (.branch 74 (.leaf 855929041) (.leaf 838139739))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 820761275) (.branch 77 (.leaf 803782340) (.leaf 787192009))) (.branch 80 (.branch 79 (.leaf 770979731) (.leaf 755135311)) (.branch 81 (.leaf 739648894) (.leaf 724510954)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 709712280) (.leaf 695243960)) (.branch 85 (.leaf 681097373) (.leaf 667264177))) (.branch 88 (.branch 87 (.leaf 653736294) (.leaf 640505906)) (.branch 89 (.leaf 627565439) (.leaf 614907556)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 602525148) (.branch 92 (.leaf 590411325) (.leaf 578559409))) (.branch 95 (.branch 94 (.leaf 566962923) (.leaf 555615586)) (.branch 96 (.leaf 544511304) (.leaf 533644165)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 523008431) (.leaf 512598532)) (.branch 100 (.leaf 502409059) (.leaf 492434760))) (.branch 103 (.branch 102 (.leaf 482670533) (.leaf 473111422)) (.branch 104 (.leaf 463752610) (.leaf 454589416))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 445617288) (.leaf 436831802)) (.branch 108 (.leaf 428228655) (.leaf 419803659))) (.branch 111 (.branch 110 (.leaf 411552744) (.leaf 403471947)) (.branch 112 (.leaf 395557411) (.leaf 387805384)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 380212209) (.leaf 372774329)) (.branch 116 (.leaf 365488279) (.leaf 358350683))) (.branch 119 (.branch 118 (.leaf 351358252) (.leaf 344507784)) (.branch 120 (.leaf 337796154) (.leaf 331220321)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 902).prefactor = (1130817635597337/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 902).cutoff/(generalMeanRows 902).c)).2 =
    (364517164073087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 902).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 902).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 902).q*(generalMeanRows 902).c/2-2 = (6041/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable278.value]
    have hcontinuation : (generalMeanRows 902).q*(generalMeanRows 902).cutoff/2-2 = (1841/936:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable292.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 902).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 902

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 902).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 902).criticalRate j.val*(generalMeanRows 902).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 902).c*(generalMeanRows 902).criticalPoint j.val)).2-
      (generalMeanRows 902).J/2-(generalMeanRows 902).error (generalMeanGrid j.val)+
      (generalMeanRows 902).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 902).c)).2-
      (generalMeanRows 902).J/2-(generalMeanRows 902).error 4 := by
  have he : (generalMeanRows 902).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 902) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 902)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0902

/-! Kernel-checked entropy margins for general spectral rectangle 903. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0903
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5326484414) (.branch 2 (.leaf 5158943744) (.leaf 4998529011))) (.branch 5 (.branch 4 (.leaf 4844843868) (.leaf 4697519739)) (.branch 6 (.leaf 4556213385) (.leaf 4420604740)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4290394971) (.leaf 4165304738)) (.branch 10 (.leaf 4045072637) (.leaf 3929453789))) (.branch 13 (.branch 12 (.leaf 3818218563) (.leaf 3711151426)) (.branch 14 (.leaf 3608049896) (.leaf 3508723586))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3412993339) (.branch 17 (.leaf 3320690429) (.leaf 3231655838))) (.branch 20 (.branch 19 (.leaf 3145739592) (.leaf 3062800143)) (.branch 21 (.leaf 2982703813) (.leaf 2905324275)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2830542073) (.leaf 2758244184)) (.branch 25 (.leaf 2688323607) (.leaf 2620678990))) (.branch 28 (.branch 27 (.leaf 2555214275) (.leaf 2491838378)) (.branch 29 (.leaf 2430464886) (.leaf 2371011776)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2313401154) (.branch 32 (.leaf 2257559013) (.leaf 2203415008))) (.branch 35 (.branch 34 (.leaf 2150902242) (.leaf 2099957068)) (.branch 36 (.leaf 2050518909) (.leaf 2002530082)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1955935637) (.leaf 1910683207)) (.branch 40 (.leaf 1866722865) (.leaf 1824006991))) (.branch 43 (.branch 42 (.leaf 1782490152) (.leaf 1742128977)) (.branch 44 (.leaf 1702882054) (.leaf 1664709823))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1627574479) (.branch 47 (.leaf 1591439885) (.leaf 1556271478))) (.branch 50 (.branch 49 (.leaf 1522036197) (.leaf 1488702398)) (.branch 51 (.leaf 1456239789) (.leaf 1424619359)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1393813313) (.leaf 1363795016)) (.branch 55 (.leaf 1334538929) (.leaf 1306020562))) (.branch 58 (.branch 57 (.leaf 1278216420) (.leaf 1251103954)) (.branch 59 (.leaf 1224661518) (.leaf 1198868323))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1173704399) (.branch 62 (.leaf 1149150555) (.leaf 1125188344))) (.branch 65 (.branch 64 (.leaf 1101800025) (.leaf 1078968536)) (.branch 66 (.leaf 1056677457) (.leaf 1034910983)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1013653899) (.leaf 992891548)) (.branch 70 (.leaf 972609810) (.leaf 952795077))) (.branch 73 (.branch 72 (.leaf 933434231) (.leaf 914514620)) (.branch 74 (.leaf 896024042) (.leaf 877950720))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 860283290) (.branch 77 (.leaf 843010778) (.leaf 826122586))) (.branch 80 (.branch 79 (.leaf 809608476) (.leaf 793458555)) (.branch 81 (.leaf 777663258) (.leaf 762213340)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 747099857) (.leaf 732314158)) (.branch 85 (.leaf 717847871) (.leaf 703692891))) (.branch 88 (.branch 87 (.leaf 689841372) (.leaf 676285715)) (.branch 89 (.leaf 663018558) (.leaf 650032769)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 637321433) (.branch 92 (.leaf 624877847) (.leaf 612695513))) (.branch 95 (.branch 94 (.leaf 600768125) (.leaf 589089567)) (.branch 96 (.leaf 577653903) (.leaf 566455372)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 555488379) (.leaf 544747492)) (.branch 100 (.leaf 534227435) (.leaf 523923081))) (.branch 103 (.branch 102 (.leaf 513829449) (.leaf 503941696)) (.branch 104 (.leaf 494255115) (.leaf 484765129))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 475467285) (.leaf 466357254)) (.branch 108 (.leaf 457430820) (.leaf 448683884))) (.branch 111 (.branch 110 (.leaf 440112454) (.leaf 431712645)) (.branch 112 (.leaf 423480672) (.leaf 415412850)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 407505591) (.leaf 399755397)) (.branch 116 (.leaf 392158861) (.leaf 384712662))) (.branch 119 (.branch 118 (.leaf 377413563) (.leaf 370258408)) (.branch 120 (.leaf 363244120) (.leaf 356367699)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 903).prefactor = (4504823902291843/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 903).cutoff/(generalMeanRows 903).c)).2 =
    (95545684893603/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 903).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 903).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 903).q*(generalMeanRows 903).c/2-2 = (5883/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable280.value]
    have hcontinuation : (generalMeanRows 903).q*(generalMeanRows 903).cutoff/2-2 = (7442/3705:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable293.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 903).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 903

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 903).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 903).criticalRate j.val*(generalMeanRows 903).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 903).c*(generalMeanRows 903).criticalPoint j.val)).2-
      (generalMeanRows 903).J/2-(generalMeanRows 903).error (generalMeanGrid j.val)+
      (generalMeanRows 903).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 903).c)).2-
      (generalMeanRows 903).J/2-(generalMeanRows 903).error 4 := by
  have he : (generalMeanRows 903).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 903) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 903)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0903

/-! Kernel-checked entropy margins for general spectral rectangle 904. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0904
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5152948839) (.branch 2 (.leaf 4983995853) (.leaf 4822308159))) (.branch 5 (.branch 4 (.leaf 4667482708) (.leaf 4519144610)) (.branch 6 (.leaf 4376944659) (.leaf 4240557149)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4109677903) (.leaf 3984022517)) (.branch 10 (.leaf 3863324777) (.leaf 3747335233))) (.branch 13 (.branch 12 (.leaf 3635819906) (.leaf 3528559122)) (.branch 14 (.leaf 3425346452) (.leaf 3325987744))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3230300244) (.branch 17 (.leaf 3138111791) (.leaf 3049260085))) (.branch 20 (.branch 19 (.leaf 2963592005) (.leaf 2880962998)) (.branch 21 (.leaf 2801236504) (.leaf 2724283432)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2649981678) (.leaf 2578215679)) (.branch 25 (.leaf 2508875996) (.leaf 2441858934))) (.branch 28 (.branch 27 (.leaf 2377066187) (.leaf 2314404513)) (.branch 29 (.leaf 2253785419) (.leaf 2195124888)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2138343105) (.branch 32 (.leaf 2083364220) (.leaf 2030116108))) (.branch 35 (.branch 34 (.leaf 1978530163) (.leaf 1928541097)) (.branch 36 (.leaf 1880086746) (.leaf 1833107904)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1787548154) (.leaf 1743353714)) (.branch 40 (.leaf 1700473298) (.leaf 1658857977))) (.branch 43 (.branch 42 (.leaf 1618461052) (.leaf 1579237939)) (.branch 44 (.leaf 1541146054) (.leaf 1504144710))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1468195017) (.branch 47 (.leaf 1433259789) (.leaf 1399303458))) (.branch 50 (.branch 49 (.leaf 1366291990) (.leaf 1334192809)) (.branch 51 (.leaf 1302974723) (.leaf 1272607853)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1243063572) (.leaf 1214314440)) (.branch 55 (.leaf 1186334146) (.leaf 1159097457))) (.branch 58 (.branch 57 (.leaf 1132580161) (.leaf 1106759020)) (.branch 59 (.leaf 1081611726) (.leaf 1057116854))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1033253821) (.branch 62 (.leaf 1010002848) (.leaf 987344919))) (.branch 65 (.branch 64 (.leaf 965261753) (.leaf 943735764)) (.branch 66 (.leaf 922750029) (.leaf 902288264)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 882334790) (.leaf 862874508)) (.branch 70 (.leaf 843892872) (.leaf 825375867))) (.branch 73 (.branch 72 (.leaf 807309984) (.leaf 789682197)) (.branch 74 (.leaf 772479945) (.leaf 755691111))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 739303999) (.branch 77 (.leaf 723307325) (.leaf 707690189))) (.branch 80 (.branch 79 (.leaf 692442069) (.leaf 677552797)) (.branch 81 (.leaf 663012551) (.leaf 648811835)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 634941470) (.leaf 621392580)) (.branch 85 (.leaf 608156580) (.leaf 595225161))) (.branch 88 (.branch 87 (.leaf 582590286) (.leaf 570244172)) (.branch 89 (.leaf 558179286) (.leaf 546388331)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 534864238) (.branch 92 (.leaf 523600160) (.leaf 512589459))) (.branch 95 (.branch 94 (.leaf 501825703) (.leaf 491302653)) (.branch 96 (.leaf 481014261) (.leaf 470954660)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 461118155) (.leaf 451499225)) (.branch 100 (.leaf 442092506) (.leaf 432892794))) (.branch 103 (.branch 102 (.leaf 423895034) (.leaf 415094318)) (.branch 104 (.leaf 406485877) (.leaf 398065080))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 389827425) (.leaf 381768536)) (.branch 108 (.leaf 373884161) (.leaf 366170163))) (.branch 111 (.branch 110 (.leaf 358622523) (.leaf 351237327)) (.branch 112 (.leaf 344010772) (.leaf 336939156)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 330018876) (.leaf 323246426)) (.branch 116 (.leaf 316618394) (.leaf 310131456))) (.branch 119 (.branch 118 (.leaf 303782378) (.leaf 297568009)) (.branch 120 (.leaf 291485280) (.leaf 285531202)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 904).prefactor = (2285972615512773/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 904).cutoff/(generalMeanRows 904).c)).2 =
    (22547084257407/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 904).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 904).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 904).q*(generalMeanRows 904).c/2-2 = (6357/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable270.value]
    have hcontinuation : (generalMeanRows 904).q*(generalMeanRows 904).cutoff/2-2 = (7442/3705:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable293.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 904).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 904

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 904).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 904).criticalRate j.val*(generalMeanRows 904).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 904).c*(generalMeanRows 904).criticalPoint j.val)).2-
      (generalMeanRows 904).J/2-(generalMeanRows 904).error (generalMeanGrid j.val)+
      (generalMeanRows 904).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 904).c)).2-
      (generalMeanRows 904).J/2-(generalMeanRows 904).error 4 := by
  have he : (generalMeanRows 904).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 904) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 904)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0904

/-! Kernel-checked entropy margins for general spectral rectangle 905. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0905
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5237190338) (.branch 2 (.leaf 5065724310) (.leaf 4901581681))) (.branch 5 (.branch 4 (.leaf 4744359344) (.leaf 4593682235)) (.branch 6 (.leaf 4449200882) (.leaf 4310589210)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4177542593) (.leaf 4049776097)) (.branch 10 (.leaf 3927022908) (.leaf 3809032909))) (.branch 13 (.branch 12 (.leaf 3695571399) (.leaf 3586417928)) (.branch 14 (.leaf 3481365247) (.leaf 3380218343))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3282793567) (.branch 17 (.leaf 3188917836) (.leaf 3098427897))) (.branch 20 (.branch 19 (.leaf 3011169662) (.leaf 2926997589)) (.branch 21 (.leaf 2845774118) (.leaf 2767369149)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2691659561) (.leaf 2618528771)) (.branch 25 (.leaf 2547866318) (.leaf 2479567487))) (.branch 28 (.branch 27 (.leaf 2413532958) (.leaf 2349668473)) (.branch 29 (.leaf 2287884539) (.leaf 2228096141)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2170222480) (.branch 32 (.leaf 2114186731) (.leaf 2059915810))) (.branch 35 (.branch 34 (.leaf 2007340163) (.leaf 1956393565)) (.branch 36 (.leaf 1907012939) (.leaf 1859138174)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1812711968) (.leaf 1767679672)) (.branch 40 (.leaf 1723989146) (.leaf 1681590628))) (.branch 43 (.branch 42 (.leaf 1640436605) (.leaf 1600481693)) (.branch 44 (.leaf 1561682530) (.leaf 1523997666))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1487387468) (.branch 47 (.leaf 1451814026) (.leaf 1417241065))) (.branch 50 (.branch 49 (.leaf 1383633863) (.leaf 1350959173)) (.branch 51 (.leaf 1319185148) (.leaf 1288281276)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1258218312) (.leaf 1228968214)) (.branch 55 (.leaf 1200504088) (.leaf 1172800134))) (.branch 58 (.branch 57 (.leaf 1145831588) (.leaf 1119574680)) (.branch 59 (.leaf 1094006581) (.leaf 1069105363))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1044849954) (.branch 62 (.leaf 1021220102) (.leaf 998196334))) (.branch 65 (.branch 64 (.leaf 975759922) (.leaf 953892850)) (.branch 66 (.leaf 932577778) (.leaf 911798018)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 891537501) (.leaf 871780747)) (.branch 70 (.leaf 852512846) (.leaf 833719427))) (.branch 73 (.branch 72 (.leaf 815386639) (.leaf 797501126)) (.branch 74 (.leaf 780050004) (.leaf 763020846))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 746401660) (.branch 77 (.leaf 730180868) (.leaf 714347295))) (.branch 80 (.branch 79 (.leaf 698890145) (.leaf 683798991)) (.branch 81 (.leaf 669063758) (.leaf 654674707)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 640622425) (.leaf 626897808)) (.branch 85 (.leaf 613492050) (.leaf 600396635))) (.branch 88 (.branch 87 (.leaf 587603318) (.leaf 575104122)) (.branch 89 (.leaf 562891322) (.leaf 550957438)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 539295224) (.branch 92 (.leaf 527897664) (.leaf 516757954))) (.branch 95 (.branch 94 (.leaf 505869503) (.leaf 495225920)) (.branch 96 (.leaf 484821009) (.leaf 474648760)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 464703342) (.leaf 454979100)) (.branch 100 (.leaf 445470544) (.leaf 436172346))) (.branch 103 (.branch 102 (.leaf 427079334) (.leaf 418186484)) (.branch 104 (.leaf 409488918) (.leaf 400981898))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 392660819) (.leaf 384521208)) (.branch 108 (.leaf 376558717) (.leaf 368769118))) (.branch 111 (.branch 110 (.leaf 361148303) (.leaf 353692274)) (.branch 112 (.leaf 346397145) (.leaf 339259136)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332274566) (.leaf 325439859)) (.branch 116 (.leaf 318751528) (.leaf 312206185))) (.branch 119 (.branch 118 (.leaf 305800529) (.leaf 299531344)) (.branch 120 (.leaf 293395502) (.leaf 287389954)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 905).prefactor = (229660806242047/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 905).cutoff/(generalMeanRows 905).c)).2 =
    (350282048251219/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 905).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 905).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 905).q*(generalMeanRows 905).c/2-2 = (6357/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable270.value]
    have hcontinuation : (generalMeanRows 905).q*(generalMeanRows 905).cutoff/2-2 = (1841/936:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable292.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 905).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 905

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 905).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 905).criticalRate j.val*(generalMeanRows 905).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 905).c*(generalMeanRows 905).criticalPoint j.val)).2-
      (generalMeanRows 905).J/2-(generalMeanRows 905).error (generalMeanGrid j.val)+
      (generalMeanRows 905).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 905).c)).2-
      (generalMeanRows 905).J/2-(generalMeanRows 905).error 4 := by
  have he : (generalMeanRows 905).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 905) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 905)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0905

/-! Kernel-checked entropy margins for general spectral rectangle 906. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0906
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5359284685) (.branch 2 (.leaf 5192299536) (.leaf 5032389032))) (.branch 5 (.branch 4 (.leaf 4879159599) (.leaf 4732245269)) (.branch 6 (.leaf 4591305260) (.leaf 4456021824)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4326098317) (.leaf 4201257472)) (.branch 10 (.leaf 4081239843) (.leaf 3965802410))) (.branch 13 (.branch 12 (.leaf 3854717302) (.leaf 3747770660)) (.branch 14 (.leaf 3644761588) (.leaf 3545501208))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3449811797) (.branch 17 (.leaf 3357525994) (.leaf 3268486079))) (.branch 20 (.branch 19 (.leaf 3182543313) (.leaf 3099557327)) (.branch 21 (.leaf 3019395563) (.leaf 2941932762)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2867050487) (.leaf 2794636684)) (.branch 25 (.leaf 2724585279) (.leaf 2656795801))) (.branch 28 (.branch 27 (.leaf 2591173034) (.leaf 2527626695)) (.branch 29 (.leaf 2466071137) (.leaf 2406425066)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2348611285) (.branch 32 (.leaf 2292556450) (.leaf 2238190849))) (.branch 35 (.branch 34 (.leaf 2185448188) (.leaf 2134265396)) (.branch 36 (.leaf 2084582445) (.leaf 2036342175)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1989490135) (.leaf 1943974433)) (.branch 40 (.leaf 1899745595) (.leaf 1856756434))) (.branch 43 (.branch 42 (.leaf 1814961926) (.leaf 1774319093)) (.branch 44 (.leaf 1734786896) (.leaf 1696326130))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1658899328) (.branch 47 (.leaf 1622470674) (.leaf 1587005911))) (.branch 50 (.branch 49 (.leaf 1552472269) (.leaf 1518838381)) (.branch 51 (.leaf 1486074217) (.leaf 1454151016)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1423041220) (.leaf 1392718418)) (.branch 55 (.leaf 1363157286) (.leaf 1334333536))) (.branch 58 (.branch 57 (.leaf 1306223865) (.leaf 1278805904)) (.branch 59 (.leaf 1252058181) (.leaf 1225960069))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1200491752) (.branch 62 (.leaf 1175634185) (.leaf 1151369058))) (.branch 65 (.branch 64 (.leaf 1127678761) (.leaf 1104546351)) (.branch 66 (.leaf 1081955526) (.leaf 1059890589)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1038336426) (.leaf 1017278477)) (.branch 70 (.leaf 996702711) (.leaf 976595605))) (.branch 73 (.branch 72 (.leaf 956944119) (.leaf 937735675)) (.branch 74 (.leaf 918958140) (.leaf 900599801))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 882649353) (.branch 77 (.leaf 865095878) (.leaf 847928830))) (.branch 80 (.branch 79 (.leaf 831138016) (.leaf 814713587)) (.branch 81 (.leaf 798646021) (.leaf 782926107)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 767544935) (.leaf 752493884)) (.branch 85 (.leaf 737764610) (.leaf 723349033))) (.branch 88 (.branch 87 (.leaf 709239328) (.leaf 695427917)) (.branch 89 (.leaf 681907455) (.leaf 668670822)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 655711119) (.branch 92 (.leaf 643021653) (.leaf 630595934))) (.branch 95 (.branch 94 (.leaf 618427662) (.leaf 606510727)) (.branch 96 (.leaf 594839197) (.leaf 583407310)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 572209475) (.leaf 561240257)) (.branch 100 (.leaf 550494376) (.leaf 539966704))) (.branch 103 (.branch 102 (.leaf 529652253) (.leaf 519546175)) (.branch 104 (.leaf 509643755) (.leaf 499940408))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 490431673) (.leaf 481113208)) (.branch 108 (.leaf 471980789) (.leaf 463030304))) (.branch 111 (.branch 110 (.leaf 454257749) (.leaf 445659224)) (.branch 112 (.leaf 437230933) (.leaf 428969175)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 420870347) (.leaf 412930935)) (.branch 116 (.leaf 405147517) (.leaf 397516755))) (.branch 119 (.branch 118 (.leaf 390035395) (.leaf 382700264)) (.branch 120 (.leaf 375508267) (.leaf 368456386)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 906).prefactor = (4503505231216009/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 906).cutoff/(generalMeanRows 906).c)).2 =
    (193457414564233/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 906).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 906).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 906).q*(generalMeanRows 906).c/2-2 = (73/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable024.value]
    have hcontinuation : (generalMeanRows 906).q*(generalMeanRows 906).cutoff/2-2 = (307/152:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable294.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 906).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 906

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 906).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 906).criticalRate j.val*(generalMeanRows 906).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 906).c*(generalMeanRows 906).criticalPoint j.val)).2-
      (generalMeanRows 906).J/2-(generalMeanRows 906).error (generalMeanGrid j.val)+
      (generalMeanRows 906).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 906).c)).2-
      (generalMeanRows 906).J/2-(generalMeanRows 906).error 4 := by
  have he : (generalMeanRows 906).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 906) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 906)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0906

/-! Kernel-checked entropy margins for general spectral rectangle 907. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0907
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4988433581) (.branch 2 (.leaf 4818338719) (.leaf 4655646822))) (.branch 5 (.branch 4 (.leaf 4499947833) (.leaf 4350860252)) (.branch 6 (.leaf 4208028637) (.leaf 4071121388)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3939828752) (.leaf 3813861041)) (.branch 10 (.leaf 3692947032) (.leaf 3576832517))) (.branch 13 (.branch 12 (.leaf 3465278997) (.leaf 3358062499)) (.branch 14 (.leaf 3254972502) (.leaf 3155810955))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3060391388) (.branch 17 (.leaf 2968538096) (.leaf 2880085392))) (.branch 20 (.branch 19 (.leaf 2794876926) (.leaf 2712765055)) (.branch 21 (.leaf 2633610266) (.leaf 2557280644)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2483651383) (.leaf 2412604331)) (.branch 25 (.leaf 2344027572) (.leaf 2277815039))) (.branch 28 (.branch 27 (.leaf 2213866151) (.leaf 2152085486)) (.branch 29 (.leaf 2092382461) (.leaf 2034671056)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1978869535) (.branch 32 (.leaf 1924900201) (.leaf 1872689164))) (.branch 35 (.branch 34 (.leaf 1822166121) (.leaf 1773264151)) (.branch 36 (.leaf 1725919532) (.leaf 1680071555)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1635662364) (.leaf 1592636796)) (.branch 40 (.leaf 1550942237) (.leaf 1510528484))) (.branch 43 (.branch 42 (.leaf 1471347619) (.leaf 1433353882)) (.branch 44 (.leaf 1396503565) (.leaf 1360754900))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1326067961) (.branch 47 (.leaf 1292404566) (.leaf 1259728194))) (.branch 50 (.branch 49 (.leaf 1228003896) (.leaf 1197198217)) (.branch 51 (.leaf 1167279123) (.leaf 1138215929)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1109979234) (.leaf 1082540856)) (.branch 55 (.leaf 1055873775) (.leaf 1029952077))) (.branch 58 (.branch 57 (.leaf 1004750899) (.leaf 980246380)) (.branch 59 (.leaf 956415614) (.leaf 933236606))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 910688226) (.branch 62 (.leaf 888750174) (.leaf 867402937))) (.branch 65 (.branch 64 (.leaf 846627756) (.leaf 826406590)) (.branch 66 (.leaf 806722084) (.leaf 787557539)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 768896884) (.leaf 750724641)) (.branch 70 (.leaf 733025911) (.leaf 715786335))) (.branch 73 (.branch 72 (.leaf 698992083) (.leaf 682629822)) (.branch 74 (.leaf 666686700) (.leaf 651150321))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 636008732) (.branch 77 (.leaf 621250397) (.leaf 606864185))) (.branch 80 (.branch 79 (.leaf 592839351) (.leaf 579165520)) (.branch 81 (.leaf 565832672) (.leaf 552831129)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 540151536) (.leaf 527784857)) (.branch 85 (.leaf 515722352) (.leaf 503955573))) (.branch 88 (.branch 87 (.leaf 492476349) (.leaf 481276776)) (.branch 89 (.leaf 470349205) (.leaf 459686236)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 449280703) (.branch 92 (.leaf 439125669) (.leaf 429214418))) (.branch 95 (.branch 94 (.leaf 419540441) (.leaf 410097436)) (.branch 96 (.leaf 400879294) (.leaf 391880094)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 383094099) (.leaf 374515744)) (.branch 100 (.leaf 366139633) (.leaf 357960532))) (.branch 103 (.branch 102 (.leaf 349973364) (.leaf 342173203)) (.branch 104 (.leaf 334555267) (.leaf 327114916))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 319847646) (.leaf 312749082)) (.branch 108 (.leaf 305814975) (.leaf 299041201))) (.branch 111 (.branch 110 (.leaf 292423750) (.leaf 285958729)) (.branch 112 (.leaf 279642353) (.leaf 273470944)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 267440927) (.leaf 261548826)) (.branch 116 (.leaf 255791262) (.leaf 250164947))) (.branch 119 (.branch 118 (.leaf 244666686) (.leaf 239293368)) (.branch 120 (.leaf 234041969) (.leaf 228909546)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 907).prefactor = (580008332425129/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 907).cutoff/(generalMeanRows 907).c)).2 =
    (169886778824659/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 907).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 907).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 907).q*(generalMeanRows 907).c/2-2 = (6831/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable285.value]
    have hcontinuation : (generalMeanRows 907).q*(generalMeanRows 907).cutoff/2-2 = (7442/3705:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable293.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 907).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 907

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 907).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 907).criticalRate j.val*(generalMeanRows 907).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 907).c*(generalMeanRows 907).criticalPoint j.val)).2-
      (generalMeanRows 907).J/2-(generalMeanRows 907).error (generalMeanGrid j.val)+
      (generalMeanRows 907).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 907).c)).2-
      (generalMeanRows 907).J/2-(generalMeanRows 907).error 4 := by
  have he : (generalMeanRows 907).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 907) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 907)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0907

/-! Kernel-checked entropy margins for general spectral rectangle 908. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0908
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5268387345) (.branch 2 (.leaf 5101791167) (.leaf 4942323697))) (.branch 5 (.branch 4 (.leaf 4789585612) (.leaf 4643205687)) (.branch 6 (.leaf 4502838343) (.leaf 4368161447)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4238874355) (.leaf 4114696151)) (.branch 10 (.leaf 3995364060) (.leaf 3880632027))) (.branch 13 (.branch 12 (.leaf 3770269420) (.leaf 3664059864)) (.branch 14 (.leaf 3561800178) (.leaf 3463299405))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3368377936) (.branch 17 (.leaf 3276866701) (.leaf 3188606432))) (.branch 20 (.branch 19 (.leaf 3103446988) (.leaf 3021246736)) (.branch 21 (.leaf 2941871979) (.leaf 2865196431)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2791100731) (.leaf 2719472000)) (.branch 25 (.leaf 2650203424) (.leaf 2583193873))) (.branch 28 (.branch 27 (.leaf 2518347544) (.leaf 2455573635)) (.branch 29 (.leaf 2394786039) (.leaf 2335903059)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2278847144) (.branch 32 (.leaf 2223544643) (.leaf 2169925579))) (.branch 35 (.branch 34 (.leaf 2117923430) (.leaf 2067474933)) (.branch 36 (.leaf 2018519896) (.leaf 1971001027)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1924863766) (.leaf 1880056135)) (.branch 40 (.leaf 1836528596) (.leaf 1794233916))) (.branch 43 (.branch 42 (.leaf 1753127040) (.leaf 1713164976)) (.branch 44 (.leaf 1674306683) (.leaf 1636512966))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1599746379) (.branch 47 (.leaf 1563971134) (.leaf 1529153014))) (.branch 50 (.branch 49 (.leaf 1495259291) (.leaf 1462258650)) (.branch 51 (.leaf 1430121117) (.leaf 1398817991)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1368321777) (.leaf 1338606133)) (.branch 55 (.leaf 1309645803) (.leaf 1281416572))) (.branch 58 (.branch 57 (.leaf 1253895208) (.leaf 1227059421)) (.branch 59 (.leaf 1200887809) (.leaf 1175359825))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1150455727) (.branch 62 (.leaf 1126156547) (.leaf 1102444049))) (.branch 65 (.branch 64 (.leaf 1079300700) (.leaf 1056709631)) (.branch 66 (.leaf 1034654613) (.leaf 1013120022)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 992090816) (.leaf 971552505)) (.branch 70 (.leaf 951491128) (.leaf 931893229))) (.branch 73 (.branch 72 (.leaf 912745836) (.leaf 894036435)) (.branch 74 (.leaf 875752957) (.leaf 857883752))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 840417575) (.branch 77 (.leaf 823343569) (.leaf 806651243))) (.branch 80 (.branch 79 (.leaf 790330464) (.leaf 774371436)) (.branch 81 (.leaf 758764692) (.leaf 743501071)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 728571718) (.leaf 713968058)) (.branch 85 (.leaf 699681796) (.leaf 685704901))) (.branch 88 (.branch 87 (.leaf 672029592) (.leaf 658648335)) (.branch 89 (.leaf 645553829) (.leaf 632738998)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 620196983) (.branch 92 (.leaf 607921130) (.leaf 595904988))) (.branch 95 (.branch 94 (.leaf 584142298) (.leaf 572626985)) (.branch 96 (.leaf 561353153) (.leaf 550315077)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 539507198) (.leaf 528924117)) (.branch 100 (.leaf 518560588) (.leaf 508411512))) (.branch 103 (.branch 102 (.leaf 498471935) (.leaf 488737040)) (.branch 104 (.leaf 479202141) (.leaf 469862684))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 460714236) (.leaf 451752485)) (.branch 108 (.leaf 442973235) (.leaf 434372401))) (.branch 111 (.branch 110 (.leaf 425946006) (.leaf 417690178)) (.branch 112 (.leaf 409601147) (.leaf 401675238)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 393908873) (.leaf 386298565)) (.branch 116 (.leaf 378840916) (.leaf 371532612))) (.branch 119 (.branch 118 (.leaf 364370425) (.leaf 357351205)) (.branch 120 (.leaf 350471882) (.leaf 343729461)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 908).prefactor = (284214854227573/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 908).cutoff/(generalMeanRows 908).c)).2 =
    (390268661226897/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 908).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 908).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 908).q*(generalMeanRows 908).c/2-2 = (1499/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable283.value]
    have hcontinuation : (generalMeanRows 908).q*(generalMeanRows 908).cutoff/2-2 = (3722/1805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable295.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 908).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 908

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 908).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 908).criticalRate j.val*(generalMeanRows 908).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 908).c*(generalMeanRows 908).criticalPoint j.val)).2-
      (generalMeanRows 908).J/2-(generalMeanRows 908).error (generalMeanGrid j.val)+
      (generalMeanRows 908).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 908).c)).2-
      (generalMeanRows 908).J/2-(generalMeanRows 908).error 4 := by
  have he : (generalMeanRows 908).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 908) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 908)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0908

/-! Kernel-checked entropy margins for general spectral rectangle 909. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0909
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5185056578) (.branch 2 (.leaf 5016623928) (.leaf 4855405458))) (.branch 5 (.branch 4 (.leaf 4701000943) (.leaf 4553038141)) (.branch 6 (.leaf 4411170345) (.leaf 4275074203)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4144447760) (.leaf 4019008714)) (.branch 10 (.leaf 3898492838) (.leaf 3782652563))) (.branch 13 (.branch 12 (.leaf 3671255694) (.leaf 3564084250)) (.branch 14 (.leaf 3460933406) (.leaf 3361610535))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3265934331) (.branch 17 (.leaf 3173734011) (.leaf 3084848583))) (.branch 20 (.branch 19 (.leaf 2999126174) (.leaf 2916423414)) (.branch 21 (.leaf 2836604873) (.leaf 2759542534)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2685115316) (.leaf 2613208630)) (.branch 25 (.leaf 2543713966) (.leaf 2476528514))) (.branch 28 (.branch 27 (.leaf 2411554811) (.leaf 2348700416)) (.branch 29 (.leaf 2287877604) (.leaf 2229003084)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2171997739) (.branch 32 (.leaf 2116786378) (.leaf 2063297509))) (.branch 35 (.branch 34 (.leaf 2011463127) (.leaf 1961218513)) (.branch 36 (.leaf 1912502053) (.leaf 1865255057)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1819421604) (.leaf 1774948382)) (.branch 40 (.leaf 1731784554) (.leaf 1689881615))) (.branch 43 (.branch 42 (.leaf 1649193275) (.leaf 1609675333)) (.branch 44 (.leaf 1571285574) (.leaf 1533983659))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1497731029) (.branch 47 (.leaf 1462490814) (.leaf 1428227744))) (.branch 50 (.branch 49 (.leaf 1394908071) (.leaf 1362499486)) (.branch 51 (.leaf 1330971053) (.leaf 1300293136)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1270437338) (.leaf 1241376435)) (.branch 55 (.leaf 1213084323) (.leaf 1185535964))) (.branch 58 (.branch 57 (.leaf 1158707329) (.leaf 1132575356)) (.branch 59 (.leaf 1107117899) (.leaf 1082313689))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1058142290) (.branch 62 (.leaf 1034584058) (.leaf 1011620111))) (.branch 65 (.branch 64 (.leaf 989232286) (.leaf 967403111)) (.branch 66 (.leaf 946115774) (.leaf 925354090)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 905102473) (.leaf 885345912)) (.branch 70 (.leaf 866069945) (.leaf 847260632))) (.branch 73 (.branch 72 (.leaf 828904536) (.leaf 810988696)) (.branch 74 (.leaf 793500613) (.leaf 776428225))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 759759891) (.branch 77 (.leaf 743484372) (.leaf 727590814))) (.branch 80 (.branch 79 (.leaf 712068733) (.leaf 696907999)) (.branch 81 (.leaf 682098822) (.leaf 667631735)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 653497587) (.leaf 639687525)) (.branch 85 (.leaf 626192982) (.leaf 613005670))) (.branch 88 (.branch 87 (.leaf 600117566) (.leaf 587520900)) (.branch 89 (.leaf 575208149) (.leaf 563172025)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 551405465) (.branch 92 (.leaf 539901626) (.leaf 528653872))) (.branch 95 (.branch 94 (.leaf 517655772) (.leaf 506901087)) (.branch 96 (.leaf 496383764) (.leaf 486097933)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 476037894) (.leaf 466198118)) (.branch 100 (.leaf 456573233) (.leaf 447158025))) (.branch 103 (.branch 102 (.leaf 437947430) (.leaf 428936527)) (.branch 104 (.leaf 420120536) (.leaf 411494811))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 403054835) (.leaf 394796219)) (.branch 108 (.leaf 386714692) (.leaf 378806104))) (.branch 111 (.branch 110 (.leaf 371066415) (.leaf 363491697)) (.branch 112 (.leaf 356078125) (.leaf 348821979)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 341719637) (.leaf 334767573)) (.branch 116 (.leaf 327962353) (.leaf 321300635))) (.branch 119 (.branch 118 (.leaf 314779162) (.leaf 308394761)) (.branch 120 (.leaf 302144342) (.leaf 296024894)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 909).prefactor = (4570279016549309/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 909).cutoff/(generalMeanRows 909).c)).2 =
    (182856310738931/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 909).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 909).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 909).q*(generalMeanRows 909).c/2-2 = (1577/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable272.value]
    have hcontinuation : (generalMeanRows 909).q*(generalMeanRows 909).cutoff/2-2 = (307/152:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable294.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 909).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 909

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 909).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 909).criticalRate j.val*(generalMeanRows 909).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 909).c*(generalMeanRows 909).criticalPoint j.val)).2-
      (generalMeanRows 909).J/2-(generalMeanRows 909).error (generalMeanGrid j.val)+
      (generalMeanRows 909).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 909).c)).2-
      (generalMeanRows 909).J/2-(generalMeanRows 909).error 4 := by
  have he : (generalMeanRows 909).error 4 = errorValues 120 := by
    convert! errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 909) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 909)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0909

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock12 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 12 i) := by
  fin_cases i
  · exact EntropyRow0840.numerical
  · exact EntropyRow0841.numerical
  · exact EntropyRow0842.numerical
  · exact EntropyRow0843.numerical
  · exact EntropyRow0844.numerical
  · exact EntropyRow0845.numerical
  · exact EntropyRow0846.numerical
  · exact EntropyRow0847.numerical
  · exact EntropyRow0848.numerical
  · exact EntropyRow0849.numerical
  · exact EntropyRow0850.numerical
  · exact EntropyRow0851.numerical
  · exact EntropyRow0852.numerical
  · exact EntropyRow0853.numerical
  · exact EntropyRow0854.numerical
  · exact EntropyRow0855.numerical
  · exact EntropyRow0856.numerical
  · exact EntropyRow0857.numerical
  · exact EntropyRow0858.numerical
  · exact EntropyRow0859.numerical
  · exact EntropyRow0860.numerical
  · exact EntropyRow0861.numerical
  · exact EntropyRow0862.numerical
  · exact EntropyRow0863.numerical
  · exact EntropyRow0864.numerical
  · exact EntropyRow0865.numerical
  · exact EntropyRow0866.numerical
  · exact EntropyRow0867.numerical
  · exact EntropyRow0868.numerical
  · exact EntropyRow0869.numerical
  · exact EntropyRow0870.numerical
  · exact EntropyRow0871.numerical
  · exact EntropyRow0872.numerical
  · exact EntropyRow0873.numerical
  · exact EntropyRow0874.numerical
  · exact EntropyRow0875.numerical
  · exact EntropyRow0876.numerical
  · exact EntropyRow0877.numerical
  · exact EntropyRow0878.numerical
  · exact EntropyRow0879.numerical
  · exact EntropyRow0880.numerical
  · exact EntropyRow0881.numerical
  · exact EntropyRow0882.numerical
  · exact EntropyRow0883.numerical
  · exact EntropyRow0884.numerical
  · exact EntropyRow0885.numerical
  · exact EntropyRow0886.numerical
  · exact EntropyRow0887.numerical
  · exact EntropyRow0888.numerical
  · exact EntropyRow0889.numerical
  · exact EntropyRow0890.numerical
  · exact EntropyRow0891.numerical
  · exact EntropyRow0892.numerical
  · exact EntropyRow0893.numerical
  · exact EntropyRow0894.numerical
  · exact EntropyRow0895.numerical
  · exact EntropyRow0896.numerical
  · exact EntropyRow0897.numerical
  · exact EntropyRow0898.numerical
  · exact EntropyRow0899.numerical
  · exact EntropyRow0900.numerical
  · exact EntropyRow0901.numerical
  · exact EntropyRow0902.numerical
  · exact EntropyRow0903.numerical
  · exact EntropyRow0904.numerical
  · exact EntropyRow0905.numerical
  · exact EntropyRow0906.numerical
  · exact EntropyRow0907.numerical
  · exact EntropyRow0908.numerical
  · exact EntropyRow0909.numerical
end SingularValueBounds.KL.Certificates
