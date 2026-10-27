import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block08
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block13
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block14
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block16
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block17
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block18
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block19
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 910. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0910
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5019749163) (.branch 2 (.leaf 4850139030) (.leaf 4687881035))) (.branch 5 (.branch 4 (.leaf 4532567992) (.leaf 4383821095)) (.branch 6 (.leaf 4241287441) (.leaf 4104637821)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3973564736) (.leaf 3847780629)) (.branch 10 (.leaf 3727016291) (.leaf 3611019418))) (.branch 13 (.branch 12 (.leaf 3499553317) (.leaf 3392395725)) (.branch 14 (.leaf 3289337744) (.leaf 3190182860))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3094746066) (.branch 17 (.leaf 3002853043) (.leaf 2914339425))) (.branch 20 (.branch 19 (.leaf 2829050114) (.leaf 2746838659)) (.branch 21 (.leaf 2667566680) (.leaf 2591103342)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2517324864) (.leaf 2446114070)) (.branch 25 (.leaf 2377359975) (.leaf 2310957394))) (.branch 28 (.branch 27 (.leaf 2246806590) (.leaf 2184812940)) (.branch 29 (.leaf 2124886627) (.leaf 2066942354)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2010899079) (.branch 32 (.leaf 1956679761) (.leaf 1904211137))) (.branch 35 (.branch 34 (.leaf 1853423498) (.leaf 1804250492)) (.branch 36 (.leaf 1756628935) (.leaf 1710498632)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1665802212) (.leaf 1622484978)) (.branch 40 (.leaf 1580494757) (.leaf 1539781763))) (.branch 43 (.branch 42 (.leaf 1500298476) (.leaf 1461999515)) (.branch 44 (.leaf 1424841529) (.leaf 1388783092))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1353784598) (.branch 47 (.leaf 1319808175) (.leaf 1286817589))) (.branch 50 (.branch 49 (.leaf 1254778166) (.leaf 1223656713)) (.branch 51 (.leaf 1193421441) (.leaf 1164041899)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1135488904) (.leaf 1107734485)) (.branch 55 (.leaf 1080751817) (.leaf 1054515170))) (.branch 58 (.branch 57 (.leaf 1028999857) (.leaf 1004182181)) (.branch 59 (.leaf 980039392) (.leaf 956549638))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 933691929) (.branch 62 (.leaf 911446090) (.leaf 889792729))) (.branch 65 (.branch 64 (.leaf 868713200) (.leaf 848189567)) (.branch 66 (.leaf 828204573) (.leaf 808741611)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 789784692) (.leaf 771318422)) (.branch 70 (.leaf 753327970) (.leaf 735799048))) (.branch 73 (.branch 72 (.leaf 718717886) (.leaf 702071209)) (.branch 74 (.leaf 685846218) (.leaf 670030565))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 654612338) (.branch 77 (.leaf 639580044) (.leaf 624922586))) (.branch 80 (.branch 79 (.leaf 610629250) (.leaf 596689690)) (.branch 81 (.leaf 583093910) (.leaf 569832254)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 556895386) (.leaf 544274285)) (.branch 85 (.leaf 531960225) (.leaf 519944767))) (.branch 88 (.branch 87 (.leaf 508219749) (.leaf 496777271)) (.branch 89 (.leaf 485609689) (.leaf 474709603)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 464069847) (.branch 92 (.leaf 453683481) (.leaf 443543783))) (.branch 95 (.branch 94 (.leaf 433644241) (.leaf 423978544)) (.branch 96 (.leaf 414540573) (.leaf 405324399)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 396324270) (.leaf 387534610)) (.branch 100 (.leaf 378950007) (.leaf 370565214))) (.branch 103 (.branch 102 (.leaf 362375137) (.leaf 354374832)) (.branch 104 (.leaf 346559500) (.leaf 338924481))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 331465251) (.leaf 324177416)) (.branch 108 (.leaf 317056706) (.leaf 310098973))) (.branch 111 (.branch 110 (.leaf 303300187) (.leaf 296656432)) (.branch 112 (.leaf 290163899) (.leaf 283818887)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 277617797) (.leaf 271557128)) (.branch 116 (.leaf 265633476) (.leaf 259843530))) (.branch 119 (.branch 118 (.leaf 254184068) (.leaf 248651954)) (.branch 120 (.leaf 243244138) (.leaf 237957652)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 910).prefactor = (4638042861442621/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 910).cutoff/(generalMeanRows 910).c)).2 =
    (344950630029433/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 910).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 910).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 910).q*(generalMeanRows 910).c/2-2 = (847/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable287.value]
    have hcontinuation : (generalMeanRows 910).q*(generalMeanRows 910).cutoff/2-2 = (307/152:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable294.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 910).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 910

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 910).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 910).criticalRate j.val*(generalMeanRows 910).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 910).c*(generalMeanRows 910).criticalPoint j.val)).2-
      (generalMeanRows 910).J/2-(generalMeanRows 910).error (generalMeanGrid j.val)+
      (generalMeanRows 910).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 910).c)).2-
      (generalMeanRows 910).J/2-(generalMeanRows 910).error 4 := by
  have he : (generalMeanRows 910).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 910) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 910)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0910

/-! Kernel-checked entropy margins for general spectral rectangle 911. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0911
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5175259748) (.branch 2 (.leaf 5006993771) (.leaf 4845981380))) (.branch 5 (.branch 4 (.leaf 4691816991) (.leaf 4544123505)) (.branch 6 (.leaf 4402549811) (.leaf 4266768567)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4136474214) (.leaf 4011381195)) (.branch 10 (.leaf 3891222345) (.leaf 3775747452))) (.branch 13 (.branch 12 (.leaf 3664721946) (.leaf 3557925713)) (.branch 14 (.leaf 3455152024) (.leaf 3356206550))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3260906472) (.branch 17 (.leaf 3169079666) (.leaf 3080563952))) (.branch 20 (.branch 19 (.leaf 2995206416) (.leaf 2912862777)) (.branch 21 (.leaf 2833396811) (.leaf 2756679817)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2682590130) (.leaf 2611012663)) (.branch 25 (.leaf 2541838492) (.leaf 2474964466))) (.branch 28 (.branch 27 (.leaf 2410292850) (.leaf 2347730989)) (.branch 29 (.leaf 2287190999) (.leaf 2228589482)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2171847255) (.branch 32 (.leaf 2116889101) (.leaf 2063643541))) (.branch 35 (.branch 34 (.leaf 2012042611) (.leaf 1962021664)) (.branch 36 (.leaf 1913519179) (.leaf 1866476586)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1820838100) (.leaf 1776550564)) (.branch 40 (.leaf 1733563308) (.leaf 1691828011))) (.branch 43 (.branch 42 (.leaf 1651298572) (.leaf 1611930992)) (.branch 44 (.leaf 1573683265) (.leaf 1536515264))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1500388651) (.branch 47 (.leaf 1465266779) (.leaf 1431114602))) (.branch 50 (.branch 49 (.leaf 1397898597) (.leaf 1365586686)) (.branch 51 (.leaf 1334148159) (.leaf 1303553606)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1273774854) (.leaf 1244784906)) (.branch 55 (.leaf 1216557877) (.leaf 1189068946))) (.branch 58 (.branch 57 (.leaf 1162294302) (.leaf 1136211092)) (.branch 59 (.leaf 1110797380) (.leaf 1086032099))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1061895013) (.branch 62 (.leaf 1038366674) (.leaf 1015428390))) (.branch 65 (.branch 64 (.leaf 993062185) (.leaf 971250769)) (.branch 66 (.leaf 949977504) (.leaf 929226378)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 908981972) (.leaf 889229438)) (.branch 70 (.leaf 869954470) (.leaf 851143279))) (.branch 73 (.branch 72 (.leaf 832782577) (.leaf 814859547)) (.branch 74 (.leaf 797361825) (.leaf 780277484))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 763595011) (.branch 77 (.leaf 747303292) (.leaf 731391592))) (.branch 80 (.branch 79 (.leaf 715849542) (.leaf 700667123)) (.branch 81 (.leaf 685834652) (.leaf 671342767)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 657182412) (.leaf 643344830)) (.branch 85 (.leaf 629821546) (.leaf 616604359))) (.branch 88 (.branch 87 (.leaf 603685329) (.leaf 591056768)) (.branch 89 (.leaf 578711227) (.leaf 566641493)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 554840573) (.branch 92 (.leaf 543301691) (.leaf 532018277))) (.branch 95 (.branch 94 (.leaf 520983958) (.leaf 510192555)) (.branch 96 (.leaf 499638072) (.leaf 489314689)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 479216759) (.leaf 469338800)) (.branch 100 (.leaf 459675486) (.leaf 450221647))) (.branch 103 (.branch 102 (.leaf 440972259) (.leaf 431922440)) (.branch 104 (.leaf 423067448) (.leaf 414402671))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 405923627) (.leaf 397625956)) (.branch 108 (.leaf 389505419) (.leaf 381557891))) (.branch 111 (.branch 110 (.leaf 373779361) (.leaf 366165924)) (.branch 112 (.leaf 358713780) (.leaf 351419230)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 344278672) (.leaf 337288599)) (.branch 116 (.leaf 330445597) (.leaf 323746339))) (.branch 119 (.branch 118 (.leaf 317187584) (.leaf 310766173)) (.branch 120 (.leaf 304479031) (.leaf 298323159)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 911).prefactor = (2306233777064153/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 911).cutoff/(generalMeanRows 911).c)).2 =
    (188091960672579/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 911).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 911).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 911).q*(generalMeanRows 911).c/2-2 = (1577/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable272.value]
    have hcontinuation : (generalMeanRows 911).q*(generalMeanRows 911).cutoff/2-2 = (3722/1805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable295.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 911).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 911

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 911).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 911).criticalRate j.val*(generalMeanRows 911).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 911).c*(generalMeanRows 911).criticalPoint j.val)).2-
      (generalMeanRows 911).J/2-(generalMeanRows 911).error (generalMeanGrid j.val)+
      (generalMeanRows 911).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 911).c)).2-
      (generalMeanRows 911).J/2-(generalMeanRows 911).error 4 := by
  have he : (generalMeanRows 911).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 911) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 911)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0911

/-! Kernel-checked entropy margins for general spectral rectangle 912. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0912
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5085226817) (.branch 2 (.leaf 4915401284) (.leaf 4752954459))) (.branch 5 (.branch 4 (.leaf 4597474316) (.leaf 4448577698)) (.branch 6 (.leaf 4305907802) (.leaf 4169131924)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4037939448) (.leaf 3912040039)) (.branch 10 (.leaf 3791162020) (.leaf 3675050906))) (.branch 13 (.branch 12 (.leaf 3563468079) (.leaf 3456189589)) (.branch 14 (.leaf 3353005064) (.leaf 3253716714))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3158138434) (.branch 17 (.leaf 3066094968) (.leaf 2977421161))) (.branch 20 (.branch 19 (.leaf 2891961260) (.leaf 2809568279)) (.branch 21 (.leaf 2730103415) (.leaf 2653435506)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2579440535) (.leaf 2508001172)) (.branch 25 (.leaf 2439006346) (.leaf 2372350856))) (.branch 28 (.branch 27 (.leaf 2307935004) (.leaf 2245664258)) (.branch 29 (.leaf 2185448939) (.leaf 2127203928)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2070848395) (.branch 32 (.leaf 2016305547) (.leaf 1963502390))) (.branch 35 (.branch 34 (.leaf 1912369513) (.leaf 1862840881)) (.branch 36 (.leaf 1814853639) (.leaf 1768347943)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1723266780) (.leaf 1679555821)) (.branch 40 (.leaf 1637163269) (.leaf 1596039719))) (.branch 43 (.branch 42 (.leaf 1556138035) (.leaf 1517413224)) (.branch 44 (.leaf 1479822321) (.leaf 1443324285))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1407879897) (.branch 47 (.leaf 1373451666) (.leaf 1340003736))) (.branch 50 (.branch 49 (.leaf 1307501808) (.leaf 1275913054)) (.branch 51 (.leaf 1245206051) (.leaf 1215350701)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1186318172) (.leaf 1158080834)) (.branch 55 (.leaf 1130612196) (.leaf 1103886854))) (.branch 58 (.branch 57 (.leaf 1077880440) (.leaf 1052569565)) (.branch 59 (.leaf 1027931781) (.leaf 1003945529))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 980590100) (.branch 62 (.leaf 957845597) (.leaf 935692893))) (.branch 65 (.branch 64 (.leaf 914113599) (.leaf 893090026)) (.branch 66 (.leaf 872605159) (.leaf 852642622)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 833186647) (.leaf 814222055)) (.branch 70 (.leaf 795734220) (.leaf 777709053))) (.branch 73 (.branch 72 (.leaf 760132973) (.leaf 742992886)) (.branch 74 (.leaf 726276165) (.leaf 709970631))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 694064529) (.branch 77 (.leaf 678546517) (.leaf 663405642))) (.branch 80 (.branch 79 (.leaf 648631328) (.leaf 634213358)) (.branch 81 (.leaf 620141861) (.leaf 606407297)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 593000442) (.leaf 579912378)) (.branch 85 (.leaf 567134479) (.leaf 554658399))) (.branch 88 (.branch 87 (.leaf 542476064) (.leaf 530579656)) (.branch 89 (.leaf 518961607) (.leaf 507614589)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 496531504) (.branch 92 (.leaf 485705474) (.leaf 475129834))) (.branch 95 (.branch 94 (.leaf 464798126) (.leaf 454704086)) (.branch 96 (.leaf 444841642) (.leaf 435204905)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 425788161) (.leaf 416585866)) (.branch 100 (.leaf 407592639) (.leaf 398803259))) (.branch 103 (.branch 102 (.leaf 390212654) (.leaf 381815902)) (.branch 104 (.leaf 373608221) (.leaf 365584965))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 357741620) (.leaf 350073802)) (.branch 108 (.leaf 342577247) (.leaf 335247811))) (.branch 111 (.branch 110 (.leaf 328081466) (.leaf 321074293)) (.branch 112 (.leaf 314222483) (.leaf 307522328)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300970223) (.leaf 294562659)) (.branch 116 (.leaf 288296221) (.leaf 282167585))) (.branch 119 (.branch 118 (.leaf 276173517) (.leaf 270310865)) (.branch 120 (.leaf 264576563) (.leaf 258967623)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 912).prefactor = (4678427389840833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 912).cutoff/(generalMeanRows 912).c)).2 =
    (362294809184491/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 912).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 912).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 912).q*(generalMeanRows 912).c/2-2 = (331/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable296.value]
    have hcontinuation : (generalMeanRows 912).q*(generalMeanRows 912).cutoff/2-2 = (3722/1805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable295.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 912).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 912

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 912).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 912).criticalRate j.val*(generalMeanRows 912).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 912).c*(generalMeanRows 912).criticalPoint j.val)).2-
      (generalMeanRows 912).J/2-(generalMeanRows 912).error (generalMeanGrid j.val)+
      (generalMeanRows 912).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 912).c)).2-
      (generalMeanRows 912).J/2-(generalMeanRows 912).error 4 := by
  have he : (generalMeanRows 912).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 912) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 912)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0912

/-! Kernel-checked entropy margins for general spectral rectangle 913. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0913
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4938437334) (.branch 2 (.leaf 4767342862) (.leaf 4603727906))) (.branch 5 (.branch 4 (.leaf 4447178449) (.leaf 4297309276)) (.branch 6 (.leaf 4153761457) (.leaf 4016200111)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3884312395) (.leaf 3757805709)) (.branch 10 (.leaf 3636406079) (.leaf 3519856701))) (.branch 13 (.branch 12 (.leaf 3407916618) (.leaf 3300359532)) (.branch 14 (.leaf 3196972715) (.leaf 3097556025))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3001921008) (.branch 17 (.leaf 2909890069) (.leaf 2821295730))) (.branch 20 (.branch 19 (.leaf 2735979932) (.leaf 2653793405)) (.branch 21 (.leaf 2574595086) (.leaf 2498251582)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2424636676) (.leaf 2353630868)) (.branch 25 (.leaf 2285120957) (.leaf 2218999642))) (.branch 28 (.branch 27 (.leaf 2155165169) (.leaf 2093520987)) (.branch 29 (.leaf 2033975437) (.leaf 1976441463)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1920836343) (.branch 32 (.leaf 1867081430) (.leaf 1815101925))) (.branch 35 (.branch 34 (.leaf 1764826651) (.leaf 1716187854)) (.branch 36 (.leaf 1669121004) (.leaf 1623564624)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1579460116) (.leaf 1536751605)) (.branch 40 (.leaf 1495385796) (.leaf 1455311828))) (.branch 43 (.branch 42 (.leaf 1416481151) (.leaf 1378847400)) (.branch 44 (.leaf 1342366284) (.leaf 1306995472))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1272694501) (.branch 47 (.leaf 1239424671) (.leaf 1207148961))) (.branch 50 (.branch 49 (.leaf 1175831944) (.leaf 1145439704)) (.branch 51 (.leaf 1115939763) (.leaf 1087301011)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1059493635) (.leaf 1032489060)) (.branch 55 (.leaf 1006259888) (.leaf 980779839))) (.branch 58 (.branch 57 (.leaf 956023699) (.leaf 931967272)) (.branch 59 (.leaf 908587328) (.leaf 885861559))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 863768539) (.branch 62 (.leaf 842287679) (.leaf 821399190))) (.branch 65 (.branch 64 (.leaf 801084048) (.leaf 781323959)) (.branch 66 (.leaf 762101323) (.leaf 743399208)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 725201315) (.leaf 707491956)) (.branch 70 (.leaf 690256019) (.leaf 673478953))) (.branch 73 (.branch 72 (.leaf 657146734) (.leaf 641245850)) (.branch 74 (.leaf 625763274) (.leaf 610686445))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 596003249) (.branch 77 (.leaf 581701999) (.leaf 567771420))) (.branch 80 (.branch 79 (.leaf 554200627) (.leaf 540979113)) (.branch 81 (.leaf 528096733) (.leaf 515543687)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 503310508) (.leaf 491388048)) (.branch 85 (.leaf 479767466) (.leaf 468440216))) (.branch 88 (.branch 87 (.leaf 457398033) (.leaf 446632925)) (.branch 89 (.leaf 436137159) (.leaf 425903256)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 415923975) (.branch 92 (.leaf 406192309) (.leaf 396701475))) (.branch 95 (.branch 94 (.leaf 387444904) (.leaf 378416232)) (.branch 96 (.leaf 369609297) (.leaf 361018128)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 352636937) (.leaf 344460117)) (.branch 100 (.leaf 336482229) (.leaf 328698002))) (.branch 103 (.branch 102 (.leaf 321102324) (.leaf 313690236)) (.branch 104 (.leaf 306456926) (.leaf 299397729))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 292508114) (.leaf 285783686)) (.branch 108 (.leaf 279220177) (.leaf 272813444))) (.branch 111 (.branch 110 (.leaf 266559465) (.leaf 260454331)) (.branch 112 (.leaf 254494249) (.leaf 248675531)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 242994596) (.leaf 237447963)) (.branch 116 (.leaf 232032249) (.leaf 226744166))) (.branch 119 (.branch 118 (.leaf 221580518) (.leaf 216538196)) (.branch 120 (.leaf 211614180) (.leaf 206805531)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 913).prefactor = (4706811445577917/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 913).cutoff/(generalMeanRows 913).c)).2 =
    (66268995594731/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 913).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 913).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 913).q*(generalMeanRows 913).c/2-2 = (443/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable297.value]
    have hcontinuation : (generalMeanRows 913).q*(generalMeanRows 913).cutoff/2-2 = (307/152:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable294.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 913).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 913

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 913).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 913).criticalRate j.val*(generalMeanRows 913).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 913).c*(generalMeanRows 913).criticalPoint j.val)).2-
      (generalMeanRows 913).J/2-(generalMeanRows 913).error (generalMeanGrid j.val)+
      (generalMeanRows 913).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 913).c)).2-
      (generalMeanRows 913).J/2-(generalMeanRows 913).error 4 := by
  have he : (generalMeanRows 913).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 913) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 913)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0913

/-! Kernel-checked entropy margins for general spectral rectangle 914. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0914
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5246772855) (.branch 2 (.leaf 5079085000) (.leaf 4918582031))) (.branch 5 (.branch 4 (.leaf 4764861884) (.leaf 4617550785)) (.branch 6 (.leaf 4476300771) (.leaf 4340787482)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4210708191) (.leaf 4085780025)) (.branch 10 (.leaf 3965738375) (.leaf 3850335461))) (.branch 13 (.branch 12 (.leaf 3739339026) (.leaf 3632531163)) (.branch 14 (.leaf 3529707245) (.leaf 3430674950))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3335253373) (.branch 17 (.leaf 3243272217) (.leaf 3154571053))) (.branch 20 (.branch 19 (.leaf 3068998633) (.leaf 2986412272)) (.branch 21 (.leaf 2906677271) (.leaf 2829666389)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2755259355) (.leaf 2683342418)) (.branch 25 (.leaf 2613807930) (.leaf 2546553963))) (.branch 28 (.branch 27 (.leaf 2481483950) (.leaf 2418506355)) (.branch 29 (.leaf 2357534367) (.leaf 2298485610)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2241281884) (.branch 32 (.leaf 2185848910) (.leaf 2132116106))) (.branch 35 (.branch 34 (.leaf 2080016368) (.leaf 2029485871)) (.branch 36 (.leaf 1980463882) (.leaf 1932892582)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1886716905) (.leaf 1841884384)) (.branch 40 (.leaf 1798345005) (.leaf 1756051077))) (.branch 43 (.branch 42 (.leaf 1714957099) (.leaf 1675019648)) (.branch 44 (.leaf 1636197266) (.leaf 1598450350))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1561741063) (.branch 47 (.leaf 1526033234) (.leaf 1491292275))) (.branch 50 (.branch 49 (.leaf 1457485098) (.leaf 1424580039)) (.branch 51 (.leaf 1392546782) (.leaf 1361356298)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1330980770) (.leaf 1301393543)) (.branch 55 (.leaf 1272569059) (.leaf 1244482807))) (.branch 58 (.branch 57 (.leaf 1217111268) (.leaf 1190431872)) (.branch 59 (.leaf 1164422947) (.leaf 1139063681))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1114334075) (.branch 62 (.leaf 1090214910) (.leaf 1066687709))) (.branch 65 (.branch 64 (.leaf 1043734699) (.leaf 1021338784)) (.branch 66 (.leaf 999483509) (.leaf 978153034)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 957332104) (.leaf 937006022)) (.branch 70 (.leaf 917160628) (.leaf 897782271))) (.branch 73 (.branch 72 (.leaf 878857787) (.leaf 860374481)) (.branch 74 (.leaf 842320103) (.leaf 824682829))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 807451246) (.branch 77 (.leaf 790614329) (.leaf 774161431))) (.branch 80 (.branch 79 (.leaf 758082262) (.leaf 742366877)) (.branch 81 (.leaf 727005658) (.leaf 711989308)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 697308828) (.leaf 682955513)) (.branch 85 (.leaf 668920937) (.leaf 655196941))) (.branch 88 (.branch 87 (.leaf 641775624) (.leaf 628649334)) (.branch 89 (.leaf 615810653) (.leaf 603252394)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 590967589) (.branch 92 (.leaf 578949482) (.leaf 567191520))) (.branch 95 (.branch 94 (.leaf 555687345) (.leaf 544430788)) (.branch 96 (.leaf 533415860) (.leaf 522636748)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 512087809) (.leaf 501763558)) (.branch 100 (.leaf 491658670) (.leaf 481767970))) (.branch 103 (.branch 102 (.leaf 472086428) (.leaf 462609155)) (.branch 104 (.leaf 453331396) (.leaf 444248529))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 435356058) (.leaf 426649609)) (.branch 108 (.leaf 418124924) (.leaf 409777862))) (.branch 111 (.branch 110 (.leaf 401604390) (.leaf 393600584)) (.branch 112 (.leaf 385762620) (.leaf 378086778)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 370569430) (.leaf 363207044)) (.branch 116 (.leaf 355996180) (.leaf 348933482))) (.branch 119 (.branch 118 (.leaf 342015682) (.leaf 335239594)) (.branch 120 (.leaf 328602109) (.leaf 322100200)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 914).prefactor = (1151324973290739/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 914).cutoff/(generalMeanRows 914).c)).2 =
    (385412199243929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 914).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 914).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 914).q*(generalMeanRows 914).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 914).q*(generalMeanRows 914).cutoff/2-2 = (1843/888:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable298.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 914).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 914

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 914).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 914).criticalRate j.val*(generalMeanRows 914).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 914).c*(generalMeanRows 914).criticalPoint j.val)).2-
      (generalMeanRows 914).J/2-(generalMeanRows 914).error (generalMeanGrid j.val)+
      (generalMeanRows 914).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 914).c)).2-
      (generalMeanRows 914).J/2-(generalMeanRows 914).error 4 := by
  have he : (generalMeanRows 914).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 914) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 914)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0914

/-! Kernel-checked entropy margins for general spectral rectangle 915. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0915
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4920712812) (.branch 2 (.leaf 4749958513) (.leaf 4586717100))) (.branch 5 (.branch 4 (.leaf 4430569519) (.leaf 4281125994)) (.branch 6 (.leaf 4138023471) (.leaf 4000923341)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3869509398) (.leaf 3743486015)) (.branch 10 (.leaf 3622576493) (.leaf 3506521584))) (.branch 13 (.branch 12 (.leaf 3395078143) (.leaf 3288017918)) (.branch 14 (.leaf 3185126439) (.leaf 3086202020))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2991054838) (.branch 17 (.leaf 2899506096) (.leaf 2811387259))) (.branch 20 (.branch 19 (.leaf 2726539349) (.leaf 2644812300)) (.branch 21 (.leaf 2566064367) (.leaf 2490161574)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2416977217) (.leaf 2346391394)) (.branch 25 (.leaf 2278290574) (.leaf 2212567202))) (.branch 28 (.branch 27 (.leaf 2149119326) (.leaf 2087850257)) (.branch 29 (.leaf 2028668250) (.leaf 1971486206)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1916221402) (.branch 32 (.leaf 1862795227) (.leaf 1811132949))) (.branch 35 (.branch 34 (.leaf 1761163489) (.leaf 1712819214)) (.branch 36 (.leaf 1666035742) (.leaf 1620751759)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1576908848) (.leaf 1534451334)) (.branch 40 (.leaf 1493326126) (.leaf 1453482588))) (.branch 43 (.branch 42 (.leaf 1414872396) (.leaf 1377449422)) (.branch 44 (.leaf 1341169616) (.leaf 1305990897))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1271873047) (.branch 47 (.leaf 1238777621) (.leaf 1206667851))) (.branch 50 (.branch 49 (.leaf 1175508563) (.leaf 1145266095)) (.branch 51 (.leaf 1115908221) (.leaf 1087404080)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1059724109) (.leaf 1032839978)) (.branch 55 (.leaf 1006724529) (.leaf 981351722))) (.branch 58 (.branch 57 (.leaf 956696578) (.leaf 932735131)) (.branch 59 (.leaf 909444375) (.leaf 886802226))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 864787471) (.branch 62 (.leaf 843379734) (.leaf 822559433))) (.branch 65 (.branch 64 (.leaf 802307744) (.leaf 782606568)) (.branch 66 (.leaf 763438497) (.leaf 744786782)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 726635306) (.leaf 708968554)) (.branch 70 (.leaf 691771585) (.leaf 675030010))) (.branch 73 (.branch 72 (.leaf 658729965) (.leaf 642858091)) (.branch 74 (.leaf 627401510) (.leaf 612347805))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 597685000) (.branch 77 (.leaf 583401543) (.leaf 569486286))) (.branch 80 (.branch 79 (.leaf 555928471) (.leaf 542717710)) (.branch 81 (.leaf 529843973) (.leaf 517297572)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 505069147) (.leaf 493149653)) (.branch 85 (.leaf 481530348) (.leaf 470202780))) (.branch 88 (.branch 87 (.leaf 459158776) (.leaf 448390431)) (.branch 89 (.leaf 437890097) (.leaf 427650374)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 417664099) (.branch 92 (.leaf 407924340) (.leaf 398424383))) (.branch 95 (.branch 94 (.leaf 389157726) (.leaf 380118071)) (.branch 96 (.leaf 371299319) (.leaf 362695555)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 354301050) (.leaf 346110249)) (.branch 100 (.leaf 338117766) (.leaf 330318378))) (.branch 103 (.branch 102 (.leaf 322707020) (.leaf 315278776)) (.branch 104 (.leaf 308028879) (.leaf 300952702))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 294045754) (.leaf 287303674)) (.branch 108 (.leaf 280722231) (.leaf 274297314))) (.branch 111 (.branch 110 (.leaf 268024930) (.leaf 261901203)) (.branch 112 (.leaf 255922365) (.leaf 250084756)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 244384819) (.leaf 238819098)) (.branch 116 (.leaf 233384230) (.leaf 228076950))) (.branch 119 (.branch 118 (.leaf 222894081) (.leaf 217832533)) (.branch 120 (.leaf 212889304) (.leaf 208061469)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 915).prefactor = (1186332618341279/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 915).cutoff/(generalMeanRows 915).c)).2 =
    (341816277840951/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 915).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 915).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 915).q*(generalMeanRows 915).c/2-2 = (443/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable297.value]
    have hcontinuation : (generalMeanRows 915).q*(generalMeanRows 915).cutoff/2-2 = (3722/1805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable295.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 915).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 915

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 915).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 915).criticalRate j.val*(generalMeanRows 915).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 915).c*(generalMeanRows 915).criticalPoint j.val)).2-
      (generalMeanRows 915).J/2-(generalMeanRows 915).error (generalMeanGrid j.val)+
      (generalMeanRows 915).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 915).c)).2-
      (generalMeanRows 915).J/2-(generalMeanRows 915).error 4 := by
  have he : (generalMeanRows 915).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 915) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 915)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0915

/-! Kernel-checked entropy margins for general spectral rectangle 916. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0916
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4914066341) (.branch 2 (.leaf 4741429283) (.leaf 4576421119))) (.branch 5 (.branch 4 (.leaf 4418616383) (.leaf 4267619307)) (.branch 6 (.leaf 4123061230) (.leaf 3984598287)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3851909341) (.leaf 3724694130)) (.branch 10 (.leaf 3602671601) (.leaf 3485578402))) (.branch 13 (.branch 12 (.leaf 3373167524) (.leaf 3265207068)) (.branch 14 (.leaf 3161479123) (.leaf 3061778752))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2965913057) (.branch 17 (.leaf 2873700333) (.leaf 2784969292))) (.branch 20 (.branch 19 (.leaf 2699558344) (.leaf 2617314953)) (.branch 21 (.leaf 2538095025) (.leaf 2461762361)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2388188140) (.leaf 2317250452)) (.branch 25 (.leaf 2248833858) (.leaf 2182828988))) (.branch 28 (.branch 27 (.leaf 2119132163) (.leaf 2057645053)) (.branch 29 (.leaf 1998274347) (.leaf 1940931460)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1885532247) (.branch 32 (.leaf 1831996747) (.leaf 1780248941))) (.branch 35 (.branch 34 (.leaf 1730216522) (.leaf 1681830685)) (.branch 36 (.leaf 1635025930) (.leaf 1589739880)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1545913100) (.leaf 1503488943)) (.branch 40 (.leaf 1462413396) (.leaf 1422634934))) (.branch 43 (.branch 42 (.leaf 1384104393) (.leaf 1346774836)) (.branch 44 (.leaf 1310601444) (.leaf 1275541399))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1241553783) (.branch 47 (.leaf 1208599479) (.leaf 1176641077))) (.branch 50 (.branch 49 (.leaf 1145642791) (.leaf 1115570373)) (.branch 51 (.leaf 1086391039) (.leaf 1058073394)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1030587363) (.leaf 1003904128)) (.branch 55 (.leaf 977996068) (.leaf 952836694))) (.branch 58 (.branch 57 (.leaf 928400604) (.leaf 904663424)) (.branch 59 (.leaf 881601762) (.leaf 859193161))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 837416057) (.branch 62 (.leaf 816249732) (.leaf 795674284))) (.branch 65 (.branch 64 (.leaf 775670579) (.leaf 756220226)) (.branch 66 (.leaf 737305534) (.leaf 718909488)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 701015715) (.leaf 683608455)) (.branch 70 (.leaf 666672536) (.leaf 650193347))) (.branch 73 (.branch 72 (.leaf 634156813) (.leaf 618549374)) (.branch 74 (.leaf 603357960) (.leaf 588569972))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 574173260) (.branch 77 (.leaf 560156108) (.leaf 546507210))) (.branch 80 (.branch 79 (.leaf 533215659) (.leaf 520270925)) (.branch 81 (.leaf 507662843) (.leaf 495381598)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 483417707) (.leaf 471762013)) (.branch 85 (.leaf 460405663) (.leaf 449340102))) (.branch 88 (.branch 87 (.leaf 438557060) (.leaf 428048539)) (.branch 89 (.leaf 417806805) (.leaf 407824374)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 398094009) (.branch 92 (.leaf 388608701) (.leaf 379361669))) (.branch 95 (.branch 94 (.leaf 370346347) (.leaf 361556377)) (.branch 96 (.leaf 352985601) (.leaf 344628054)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 336477955) (.leaf 328529704)) (.branch 100 (.leaf 320777871) (.leaf 313217195))) (.branch 103 (.branch 102 (.leaf 305842571) (.leaf 298649053)) (.branch 104 (.leaf 291631839) (.leaf 284786275))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 278107843) (.leaf 271592159)) (.branch 108 (.leaf 265234969) (.leaf 259032144))) (.branch 111 (.branch 110 (.leaf 252979673) (.leaf 247073664)) (.branch 112 (.leaf 241310336) (.leaf 235686017)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 230197140) (.leaf 224840241)) (.branch 116 (.leaf 219611951) (.leaf 214508998))) (.branch 119 (.branch 118 (.leaf 209528203) (.leaf 204666474)) (.branch 120 (.leaf 199920804) (.leaf 195288273)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 916).prefactor = (1203297573365443/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 916).cutoff/(generalMeanRows 916).c)).2 =
    (167541122829803/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 916).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 916).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 916).q*(generalMeanRows 916).c/2-2 = (1811/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable289.value]
    have hcontinuation : (generalMeanRows 916).q*(generalMeanRows 916).cutoff/2-2 = (3722/1805:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable295.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 916).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 916

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 916).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 916).criticalRate j.val*(generalMeanRows 916).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 916).c*(generalMeanRows 916).criticalPoint j.val)).2-
      (generalMeanRows 916).J/2-(generalMeanRows 916).error (generalMeanGrid j.val)+
      (generalMeanRows 916).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 916).c)).2-
      (generalMeanRows 916).J/2-(generalMeanRows 916).error 4 := by
  have he : (generalMeanRows 916).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 916) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 916)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0916

/-! Kernel-checked entropy margins for general spectral rectangle 917. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0917
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5155134266) (.branch 2 (.leaf 4985837574) (.leaf 4823850851))) (.branch 5 (.branch 4 (.leaf 4668765681) (.leaf 4520202321)) (.branch 6 (.leaf 4377807194) (.leaf 4241250652)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4110224976) (.leaf 3984442581)) (.branch 10 (.leaf 3863634403) (.leaf 3747548439))) (.branch 13 (.branch 12 (.leaf 3635948437) (.leaf 3528612696)) (.branch 14 (.leaf 3425332988) (.leaf 3325913568))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3230170278) (.branch 17 (.leaf 3137929725) (.leaf 3049028527))) (.branch 20 (.branch 19 (.leaf 2963312626) (.leaf 2880636656)) (.branch 21 (.leaf 2800863359) (.leaf 2723863051)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2649513127) (.leaf 2577697605)) (.branch 25 (.leaf 2508306705) (.leaf 2441236459))) (.branch 28 (.branch 27 (.leaf 2376388346) (.leaf 2313668963)) (.branch 29 (.leaf 2252989707) (.leaf 2194266487)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2137419459) (.branch 32 (.leaf 2082372770) (.leaf 2029054326))) (.branch 35 (.branch 34 (.leaf 1977395575) (.leaf 1927331302)) (.branch 36 (.leaf 1878799438) (.leaf 1831740887)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1786099354) (.leaf 1741821191)) (.branch 40 (.leaf 1698855254) (.leaf 1657152762))) (.branch 43 (.branch 42 (.leaf 1616667174) (.leaf 1577354061)) (.branch 44 (.leaf 1539171001) (.leaf 1502077470))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1466034739) (.branch 47 (.leaf 1431005784) (.leaf 1396955197))) (.branch 50 (.branch 49 (.leaf 1363849103) (.leaf 1331655080)) (.branch 51 (.leaf 1300342086) (.leaf 1269880393)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1240241514) (.leaf 1211398149)) (.branch 55 (.leaf 1183324121) (.leaf 1155994326))) (.branch 58 (.branch 57 (.leaf 1129384674) (.leaf 1103472047)) (.branch 59 (.leaf 1078234249) (.leaf 1053649960))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1029698699) (.branch 62 (.leaf 1006360782) (.leaf 983617286))) (.branch 65 (.branch 64 (.leaf 961450011) (.leaf 939841450)) (.branch 66 (.leaf 918774756) (.leaf 898233711)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 878202699) (.leaf 858666680)) (.branch 70 (.leaf 839611159) (.leaf 821022170))) (.branch 73 (.branch 72 (.leaf 802886247) (.leaf 785190403)) (.branch 74 (.leaf 767922110) (.leaf 751069281))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 734620248) (.branch 77 (.leaf 718563745) (.leaf 702888893))) (.branch 80 (.branch 79 (.leaf 687585183) (.leaf 672642458)) (.branch 81 (.leaf 658050903) (.leaf 643801027)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 629883652) (.leaf 616289900)) (.branch 85 (.leaf 603011180) (.leaf 590039180))) (.branch 88 (.branch 87 (.leaf 577365850) (.leaf 564983396)) (.branch 89 (.leaf 552884271) (.leaf 541061162)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 529506983) (.branch 92 (.leaf 518214865) (.leaf 507178150))) (.branch 95 (.branch 94 (.leaf 496390382) (.leaf 485845299)) (.branch 96 (.leaf 475536825) (.leaf 465459066)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 455606301) (.leaf 445972976)) (.branch 100 (.leaf 436553700) (.leaf 427343235))) (.branch 103 (.branch 102 (.leaf 418336497) (.leaf 409528542)) (.branch 104 (.leaf 400914571) (.leaf 392489917))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 384250043) (.leaf 376190541)) (.branch 108 (.leaf 368307120) (.leaf 360595612))) (.branch 111 (.branch 110 (.leaf 353051958) (.leaf 345672212)) (.branch 112 (.leaf 338452533) (.leaf 331389184)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324478525) (.leaf 317717016)) (.branch 116 (.leaf 311101206) (.leaf 304627739))) (.branch 119 (.branch 118 (.leaf 298293343) (.leaf 292094832)) (.branch 120 (.leaf 286029101) (.leaf 280093128)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 917).prefactor = (934155443665469/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 917).cutoff/(generalMeanRows 917).c)).2 =
    (92904719277899/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 917).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 917).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 917).q*(generalMeanRows 917).c/2-2 = (1621/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable288.value]
    have hcontinuation : (generalMeanRows 917).q*(generalMeanRows 917).cutoff/2-2 = (1843/888:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable298.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 917).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 917

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 917).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 917).criticalRate j.val*(generalMeanRows 917).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 917).c*(generalMeanRows 917).criticalPoint j.val)).2-
      (generalMeanRows 917).J/2-(generalMeanRows 917).error (generalMeanGrid j.val)+
      (generalMeanRows 917).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 917).c)).2-
      (generalMeanRows 917).J/2-(generalMeanRows 917).error 4 := by
  have he : (generalMeanRows 917).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 917) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 917)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0917

/-! Kernel-checked entropy margins for general spectral rectangle 918. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0918
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5146643896) (.branch 2 (.leaf 4975378210) (.leaf 4811537323))) (.branch 5 (.branch 4 (.leaf 4654706659) (.leaf 4504500713)) (.branch 6 (.leaf 4360560516) (.leaf 4222551366)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4090160798) (.leaf 3963096768)) (.branch 10 (.leaf 3841086014) (.leaf 3723872584))) (.branch 13 (.branch 12 (.leaf 3611216496) (.leaf 3502892534)) (.branch 14 (.leaf 3398689147) (.leaf 3298407451))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3201860313) (.branch 17 (.leaf 3108871527) (.leaf 3019275043))) (.branch 20 (.branch 19 (.leaf 2932914274) (.leaf 2849641453)) (.branch 21 (.leaf 2769317043) (.leaf 2691809194)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2616993242) (.leaf 2544751247)) (.branch 25 (.leaf 2474971566) (.leaf 2407548454))) (.branch 28 (.branch 27 (.leaf 2342381702) (.leaf 2279376295)) (.branch 29 (.leaf 2218442092) (.leaf 2159493541)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2102449397) (.branch 32 (.leaf 2047232473) (.leaf 1993769402))) (.branch 35 (.branch 34 (.leaf 1941990414) (.leaf 1891829131)) (.branch 36 (.leaf 1843222375) (.leaf 1796109985)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1750434651) (.leaf 1706141754)) (.branch 40 (.leaf 1663179219) (.leaf 1621497377))) (.branch 43 (.branch 42 (.leaf 1581048834) (.leaf 1541788347)) (.branch 44 (.leaf 1503672714) (.leaf 1466660662))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1430712746) (.branch 47 (.leaf 1395791259) (.leaf 1361860134))) (.branch 50 (.branch 49 (.leaf 1328884866) (.leaf 1296832431)) (.branch 51 (.leaf 1265671209) (.leaf 1235370916)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1205902537) (.leaf 1177238260)) (.branch 55 (.leaf 1149351423) (.leaf 1122216450))) (.branch 58 (.branch 57 (.leaf 1095808806) (.leaf 1070104940)) (.branch 59 (.leaf 1045082246) (.leaf 1020719007))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 996994364) (.branch 62 (.leaf 973888270) (.leaf 951381452))) (.branch 65 (.branch 64 (.leaf 929455376) (.leaf 908092217)) (.branch 66 (.leaf 887274819) (.leaf 866986670)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 847211873) (.leaf 827935116)) (.branch 70 (.leaf 809141647) (.leaf 790817252))) (.branch 73 (.branch 72 (.leaf 772948225) (.leaf 755521353)) (.branch 74 (.leaf 738523890) (.leaf 721943540))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 705768434) (.branch 77 (.leaf 689987117) (.leaf 674588526))) (.branch 80 (.branch 79 (.leaf 659561976) (.leaf 644897144)) (.branch 81 (.leaf 630584053) (.leaf 616613059)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 602974840) (.leaf 589660376)) (.branch 85 (.leaf 576660943) (.leaf 563968101))) (.branch 88 (.branch 87 (.leaf 551573679) (.leaf 539469768)) (.branch 89 (.leaf 527648708) (.leaf 516103081)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 504825701) (.branch 92 (.leaf 493809604) (.leaf 483048041))) (.branch 95 (.branch 94 (.leaf 472534468) (.leaf 462262541)) (.branch 96 (.leaf 452226107) (.leaf 442419197)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 432836020) (.leaf 423470955)) (.branch 100 (.leaf 414318546) (.leaf 405373499))) (.branch 103 (.branch 102 (.leaf 396630671) (.leaf 388085066)) (.branch 104 (.leaf 379731833) (.leaf 371566259))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 363583763) (.leaf 355779892)) (.branch 108 (.leaf 348150321) (.leaf 340690841))) (.branch 111 (.branch 110 (.leaf 333397361) (.leaf 326265902)) (.branch 112 (.leaf 319292594) (.leaf 312473671)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 305805469) (.leaf 299284424)) (.branch 116 (.leaf 292907064) (.leaf 286670011))) (.branch 119 (.branch 118 (.leaf 280569977) (.leaf 274603759)) (.branch 120 (.leaf 268768238) (.leaf 263060377)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 918).prefactor = (4737185488318379/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 918).cutoff/(generalMeanRows 918).c)).2 =
    (72958582408239/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 918).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 918).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 918).q*(generalMeanRows 918).c/2-2 = (3319/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable299.value]
    have hcontinuation : (generalMeanRows 918).q*(generalMeanRows 918).cutoff/2-2 = (1843/888:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable298.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 918).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 918

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 918).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 918).criticalRate j.val*(generalMeanRows 918).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 918).c*(generalMeanRows 918).criticalPoint j.val)).2-
      (generalMeanRows 918).J/2-(generalMeanRows 918).error (generalMeanGrid j.val)+
      (generalMeanRows 918).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 918).c)).2-
      (generalMeanRows 918).J/2-(generalMeanRows 918).error 4 := by
  have he : (generalMeanRows 918).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 918) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 918)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0918

/-! Kernel-checked entropy margins for general spectral rectangle 919. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0919
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5083981515) (.branch 2 (.leaf 4916559774) (.leaf 4756407217))) (.branch 5 (.branch 4 (.leaf 4603114581) (.leaf 4456301484)) (.branch 6 (.leaf 4315613904) (.leaf 4180721918)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4051317694) (.leaf 3927113671)) (.branch 10 (.leaf 3807840938) (.leaf 3693247758))) (.branch 13 (.branch 12 (.leaf 3583098245) (.leaf 3477171156)) (.branch 14 (.leaf 3375258796) (.leaf 3277166024))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3182709346) (.branch 17 (.leaf 3091716082) (.leaf 3004023608))) (.branch 20 (.branch 19 (.leaf 2919478663) (.leaf 2837936705)) (.branch 21 (.leaf 2759261328) (.leaf 2683323716)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2610002149) (.leaf 2539181542)) (.branch 25 (.leaf 2470753016) (.leaf 2404613507))) (.branch 28 (.branch 27 (.leaf 2340665401) (.leaf 2278816195)) (.branch 29 (.leaf 2218978184) (.leaf 2161068169)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2105007182) (.branch 32 (.leaf 2050720241) (.leaf 1998136108))) (.branch 35 (.branch 34 (.leaf 1947187074) (.leaf 1897808749)) (.branch 36 (.leaf 1849939878) (.leaf 1803522158)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1758500069) (.leaf 1714820724)) (.branch 40 (.leaf 1672433718) (.leaf 1631290992))) (.branch 43 (.branch 42 (.leaf 1591346705) (.leaf 1552557112)) (.branch 44 (.leaf 1514880456) (.leaf 1478276853))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1442708202) (.branch 47 (.leaf 1408138083) (.leaf 1374531676))) (.branch 50 (.branch 49 (.leaf 1341855671) (.leaf 1310078196)) (.branch 51 (.leaf 1279168741) (.leaf 1249098087)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1219838245) (.leaf 1191362389)) (.branch 55 (.leaf 1163644805) (.leaf 1136660830))) (.branch 58 (.branch 57 (.leaf 1110386802) (.leaf 1084800014)) (.branch 59 (.leaf 1059878663) (.leaf 1035601813))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1011949347) (.branch 62 (.leaf 988901932) (.leaf 966440981))) (.branch 65 (.branch 64 (.leaf 944548621) (.leaf 923207653)) (.branch 66 (.leaf 902401530) (.leaf 882114318)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 862330677) (.leaf 843035827)) (.branch 70 (.leaf 824215527) (.leaf 805856049))) (.branch 73 (.branch 72 (.leaf 787944159) (.leaf 770467090)) (.branch 74 (.leaf 753412526) (.leaf 736768580))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 720523776) (.branch 77 (.leaf 704667034) (.leaf 689187650))) (.branch 80 (.branch 79 (.leaf 674075282) (.leaf 659319936)) (.branch 81 (.leaf 644911947) (.leaf 630841971)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 617100970) (.leaf 603680199)) (.branch 85 (.leaf 590571193) (.leaf 577765760))) (.branch 88 (.branch 87 (.leaf 565255966) (.leaf 553034127)) (.branch 89 (.leaf 541092800) (.leaf 529424770)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 518023047) (.branch 92 (.leaf 506880853) (.leaf 495991614))) (.branch 95 (.branch 94 (.leaf 485348957) (.leaf 474946697)) (.branch 96 (.leaf 464778832) (.leaf 454839538)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 445123162) (.leaf 435624212)) (.branch 100 (.leaf 426337358) (.leaf 417257421))) (.branch 103 (.branch 102 (.leaf 408379369) (.leaf 399698312)) (.branch 104 (.leaf 391209499) (.leaf 382908311))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 374790255) (.leaf 366850965)) (.branch 108 (.leaf 359086193) (.leaf 351491805))) (.branch 111 (.branch 110 (.leaf 344063783) (.leaf 336798212)) (.branch 112 (.leaf 329691286) (.leaf 322739298)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 315938640) (.leaf 309285797)) (.branch 116 (.leaf 302777349) (.leaf 296409963))) (.branch 119 (.branch 118 (.leaf 290180393) (.leaf 284085475)) (.branch 120 (.leaf 278122128) (.leaf 272287348)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 919).prefactor = (2345978972253181/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 919).cutoff/(generalMeanRows 919).c)).2 =
    (95509878691323/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 919).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 919).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 919).q*(generalMeanRows 919).c/2-2 = (1643/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable300.value]
    have hcontinuation : (generalMeanRows 919).q*(generalMeanRows 919).cutoff/2-2 = (461/216:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable301.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 919).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 919

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 919).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 919).criticalRate j.val*(generalMeanRows 919).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 919).c*(generalMeanRows 919).criticalPoint j.val)).2-
      (generalMeanRows 919).J/2-(generalMeanRows 919).error (generalMeanGrid j.val)+
      (generalMeanRows 919).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 919).c)).2-
      (generalMeanRows 919).J/2-(generalMeanRows 919).error 4 := by
  have he : (generalMeanRows 919).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 919) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 919)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0919

/-! Kernel-checked entropy margins for general spectral rectangle 920. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0920
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5223558146) (.branch 2 (.leaf 5051539975) (.leaf 4886990559))) (.branch 5 (.branch 4 (.leaf 4729489396) (.leaf 4578645664)) (.branch 6 (.leaf 4434095619) (.leaf 4295500282)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4162543369) (.leaf 4034929424)) (.branch 10 (.leaf 3912382154) (.leaf 3794642910))) (.branch 13 (.branch 12 (.leaf 3681469331) (.leaf 3572634099)) (.branch 14 (.leaf 3467923816) (.leaf 3367137987))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3270088076) (.branch 17 (.leaf 3176596665) (.leaf 3086496665))) (.branch 20 (.branch 19 (.leaf 2999630606) (.leaf 2915849979)) (.branch 21 (.leaf 2835014632) (.leaf 2756992214)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2681657663) (.leaf 2608892733)) (.branch 25 (.leaf 2538585556) (.leaf 2470630240))) (.branch 28 (.branch 27 (.leaf 2404926490) (.leaf 2341379264)) (.branch 29 (.leaf 2279898449) (.leaf 2220398560)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2162798464) (.branch 32 (.leaf 2107021119) (.leaf 2052993331))) (.branch 35 (.branch 34 (.leaf 2000645532) (.leaf 1949911565)) (.branch 36 (.leaf 1900728493) (.leaf 1853036411)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1806778277) (.leaf 1761899751)) (.branch 40 (.leaf 1718349043) (.leaf 1676076776))) (.branch 43 (.branch 42 (.leaf 1635035851) (.leaf 1595181321)) (.branch 44 (.leaf 1556470282) (.leaf 1518861757))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1482316597) (.branch 47 (.leaf 1446797384) (.leaf 1412268340))) (.branch 50 (.branch 49 (.leaf 1378695241) (.leaf 1346045342)) (.branch 51 (.leaf 1314287292) (.leaf 1283391072)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1253327924) (.leaf 1224070287)) (.branch 55 (.leaf 1195591739) (.leaf 1167866940))) (.branch 58 (.branch 57 (.leaf 1140871580) (.leaf 1114582327)) (.branch 59 (.leaf 1088976781) (.leaf 1064033429))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1039731604) (.branch 62 (.leaf 1016051440) (.leaf 992973843))) (.branch 65 (.branch 64 (.leaf 970480445) (.leaf 948553578)) (.branch 66 (.leaf 927176239) (.leaf 906332059)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 886005273) (.leaf 866180698)) (.branch 70 (.leaf 846843702) (.leaf 827980180))) (.branch 73 (.branch 72 (.leaf 809576534) (.leaf 791619646)) (.branch 74 (.leaf 774096862) (.leaf 756995969))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 740305178) (.branch 77 (.leaf 724013101) (.leaf 708108744))) (.branch 80 (.branch 79 (.leaf 692581478) (.leaf 677421035)) (.branch 81 (.leaf 662617486) (.leaf 648161231)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 634042982) (.leaf 620253754)) (.branch 85 (.leaf 606784851) (.leaf 593627855))) (.branch 88 (.branch 87 (.leaf 580774615) (.leaf 568217235)) (.branch 89 (.leaf 555948068) (.leaf 543959702)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 532244954) (.branch 92 (.leaf 520796859) (.leaf 509608666))) (.branch 95 (.branch 94 (.leaf 498673823) (.leaf 487985977)) (.branch 96 (.leaf 477538961) (.leaf 467326792)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 457343661) (.leaf 447583925)) (.branch 100 (.leaf 438042108) (.leaf 428712888))) (.branch 103 (.branch 102 (.leaf 419591096) (.leaf 410671708)) (.branch 104 (.leaf 401949842) (.leaf 393420751))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 385079821) (.leaf 376922564)) (.branch 108 (.leaf 368944616) (.leaf 361141731))) (.branch 111 (.branch 110 (.leaf 353509778) (.leaf 346044737)) (.branch 112 (.leaf 338742696) (.leaf 331599846)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324612481) (.leaf 317776991)) (.branch 116 (.leaf 311089859) (.leaf 304547661))) (.branch 119 (.branch 118 (.leaf 298147062) (.leaf 291884813)) (.branch 120 (.leaf 285757747) (.leaf 279762779)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 920).prefactor = (192830875321403/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 920).cutoff/(generalMeanRows 920).c)).2 =
    (95509878691323/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 920).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 920).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 920).q*(generalMeanRows 920).c/2-2 = (1643/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable300.value]
    have hcontinuation : (generalMeanRows 920).q*(generalMeanRows 920).cutoff/2-2 = (461/216:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable301.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 920).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 920

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 920).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 920).criticalRate j.val*(generalMeanRows 920).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 920).c*(generalMeanRows 920).criticalPoint j.val)).2-
      (generalMeanRows 920).J/2-(generalMeanRows 920).error (generalMeanGrid j.val)+
      (generalMeanRows 920).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 920).c)).2-
      (generalMeanRows 920).J/2-(generalMeanRows 920).error 4 := by
  have he : (generalMeanRows 920).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 920) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 920)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0920

/-! Kernel-checked entropy margins for general spectral rectangle 921. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0921
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5282873992) (.branch 2 (.leaf 5106592063) (.leaf 4937995473))) (.branch 5 (.branch 4 (.leaf 4776651791) (.leaf 4622159070)) (.branch 6 (.leaf 4474143185) (.leaf 4332255452)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4196170500) (.leaf 4065584363)) (.branch 10 (.leaf 3940212759) (.leaf 3819789542))) (.branch 13 (.branch 12 (.leaf 3704065297) (.leaf 3592806074)) (.branch 14 (.leaf 3485792228) (.leaf 3382817369))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3283687409) (.branch 17 (.leaf 3188219681) (.leaf 3096242139))) (.branch 20 (.branch 19 (.leaf 3007592627) (.leaf 2922118200)) (.branch 21 (.leaf 2839674506) (.leaf 2760125216)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2683341499) (.leaf 2609201529)) (.branch 25 (.leaf 2537590046) (.leaf 2468397933))) (.branch 28 (.branch 27 (.leaf 2401521833) (.leaf 2336863792)) (.branch 29 (.leaf 2274330930) (.leaf 2213835129)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2155292749) (.branch 32 (.leaf 2098624361) (.leaf 2043754499))) (.branch 35 (.branch 34 (.leaf 1990611426) (.leaf 1939126922)) (.branch 36 (.leaf 1889236078) (.leaf 1840877112)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1793991188) (.leaf 1748522252)) (.branch 40 (.leaf 1704416883) (.leaf 1661624139))) (.branch 43 (.branch 42 (.leaf 1620095428) (.leaf 1579784380)) (.branch 44 (.leaf 1540646726) (.leaf 1502640183))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1465724357) (.branch 47 (.leaf 1429860636) (.leaf 1395012098))) (.branch 50 (.branch 49 (.leaf 1361143428) (.leaf 1328220832)) (.branch 51 (.leaf 1296211958) (.leaf 1265085826)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1234812757) (.leaf 1205364309)) (.branch 55 (.leaf 1176713216) (.leaf 1148833327))) (.branch 58 (.branch 57 (.leaf 1121699556) (.leaf 1095287826)) (.branch 59 (.leaf 1069575023) (.leaf 1044538950))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1020158281) (.branch 62 (.leaf 996412522) (.leaf 973281972))) (.branch 65 (.branch 64 (.leaf 950747685) (.leaf 928791435)) (.branch 66 (.leaf 907395683) (.leaf 886543548)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 866218773) (.leaf 846405700)) (.branch 70 (.leaf 827089245) (.leaf 808254865))) (.branch 73 (.branch 72 (.leaf 789888544) (.leaf 771976763)) (.branch 74 (.leaf 754506481) (.leaf 737465113))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 720840515) (.branch 77 (.leaf 704620957) (.leaf 688795115))) (.branch 80 (.branch 79 (.leaf 673352046) (.leaf 658281179)) (.branch 81 (.leaf 643572292) (.leaf 629215507)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 615201267) (.leaf 601520328)) (.branch 85 (.leaf 588163749) (.leaf 575122871))) (.branch 88 (.branch 87 (.leaf 562389316) (.leaf 549954970)) (.branch 89 (.leaf 537811973) (.leaf 525952712)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 514369809) (.branch 92 (.leaf 503056115) (.leaf 492004697))) (.branch 95 (.branch 94 (.leaf 481208834) (.leaf 470662007)) (.branch 96 (.leaf 460357892) (.leaf 450290353)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 440453435) (.leaf 430841359)) (.branch 100 (.leaf 421448512) (.leaf 412269445))) (.branch 103 (.branch 102 (.leaf 403298866) (.leaf 394531633)) (.branch 104 (.leaf 385962752) (.leaf 377587367))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 369400760) (.leaf 361398346)) (.branch 108 (.leaf 353575665) (.leaf 345928380))) (.branch 111 (.branch 110 (.leaf 338452273) (.leaf 331143242)) (.branch 112 (.leaf 323997296) (.leaf 317010549)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 310179223) (.leaf 303499638)) (.branch 116 (.leaf 296968212) (.leaf 290581459))) (.branch 119 (.branch 118 (.leaf 284335983) (.leaf 278228477)) (.branch 120 (.leaf 272255720) (.leaf 266414576)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 921).prefactor = (619140288103823/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 921).cutoff/(generalMeanRows 921).c)).2 =
    (46916010022163/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 921).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 921).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 921).q*(generalMeanRows 921).c/2-2 = (1681/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable302.value]
    have hcontinuation : (generalMeanRows 921).q*(generalMeanRows 921).cutoff/2-2 = (461/216:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable301.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 921).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 921

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 921).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 921).criticalRate j.val*(generalMeanRows 921).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 921).c*(generalMeanRows 921).criticalPoint j.val)).2-
      (generalMeanRows 921).J/2-(generalMeanRows 921).error (generalMeanGrid j.val)+
      (generalMeanRows 921).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 921).c)).2-
      (generalMeanRows 921).J/2-(generalMeanRows 921).error 4 := by
  have he : (generalMeanRows 921).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 921) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 921)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0921

/-! Kernel-checked entropy margins for general spectral rectangle 922. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0922
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7532045844) (.branch 2 (.leaf 7310243302) (.leaf 7097005940))) (.branch 5 (.branch 4 (.leaf 6891895570) (.leaf 6694504025)) (.branch 6 (.leaf 6504450438) (.leaf 6321378828)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6144955959) (.leaf 5974869432)) (.branch 10 (.leaf 5810825981) (.leaf 5652549944))) (.branch 13 (.branch 12 (.leaf 5499781892) (.leaf 5352277387)) (.branch 14 (.leaf 5209805871) (.leaf 5072149643))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4939102951) (.branch 17 (.leaf 4810471147) (.leaf 4686069929))) (.branch 20 (.branch 19 (.leaf 4565724642) (.leaf 4449269643)) (.branch 21 (.leaf 4336547711) (.leaf 4227409516)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4121713122) (.leaf 4019323527)) (.branch 25 (.leaf 3920112249) (.leaf 3823956934))) (.branch 28 (.branch 27 (.leaf 3730740993) (.leaf 3640353274)) (.branch 29 (.leaf 3552687744) (.leaf 3467643208)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3385123037) (.branch 32 (.leaf 3305034917) (.leaf 3227290616))) (.branch 35 (.branch 34 (.leaf 3151805770) (.leaf 3078499672)) (.branch 36 (.leaf 3007295087) (.leaf 2938118072)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2870897806) (.leaf 2805566435)) (.branch 40 (.leaf 2742058923) (.leaf 2680312914))) (.branch 43 (.branch 42 (.leaf 2620268599) (.leaf 2561868597)) (.branch 44 (.leaf 2505057835) (.leaf 2449783439))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2395994633) (.branch 47 (.leaf 2343642639) (.leaf 2292680586))) (.branch 50 (.branch 49 (.leaf 2243063423) (.leaf 2194747833)) (.branch 51 (.leaf 2147692162) (.leaf 2101856337)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2057201802) (.leaf 2013691447)) (.branch 55 (.leaf 1971289548) (.leaf 1929961706))) (.branch 58 (.branch 57 (.leaf 1889674788) (.leaf 1850396877)) (.branch 59 (.leaf 1812097216) (.leaf 1774746164))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1738315143) (.branch 62 (.leaf 1702776600) (.leaf 1668103962))) (.branch 65 (.branch 64 (.leaf 1634271596) (.leaf 1601254769)) (.branch 66 (.leaf 1569029614) (.leaf 1537573095)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1506862971) (.leaf 1476877767)) (.branch 70 (.leaf 1447596744) (.leaf 1418999868))) (.branch 73 (.branch 72 (.leaf 1391067782) (.leaf 1363781783)) (.branch 74 (.leaf 1337123792) (.leaf 1311076335))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1285622515) (.branch 77 (.leaf 1260745995) (.leaf 1236430970))) (.branch 80 (.branch 79 (.leaf 1212662154) (.leaf 1189424757)) (.branch 81 (.leaf 1166704465) (.leaf 1144487426)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1122760230) (.leaf 1101509893)) (.branch 85 (.leaf 1080723844) (.leaf 1060389907))) (.branch 88 (.branch 87 (.leaf 1040496287) (.leaf 1021031556)) (.branch 89 (.leaf 1001984644) (.leaf 983344820)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 965101682) (.branch 92 (.leaf 947245148) (.leaf 929765443))) (.branch 95 (.branch 94 (.leaf 912653085) (.leaf 895898879)) (.branch 96 (.leaf 879493908) (.leaf 863429516)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 847697309) (.leaf 832289136)) (.branch 100 (.leaf 817197090) (.leaf 802413491))) (.branch 103 (.branch 102 (.leaf 787930886) (.leaf 773742036)) (.branch 104 (.leaf 759839910) (.leaf 746217679))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 732868710) (.leaf 719786556)) (.branch 108 (.leaf 706964955) (.leaf 694397819))) (.branch 111 (.branch 110 (.leaf 682079230) (.leaf 670003436)) (.branch 112 (.leaf 658164843) (.leaf 646558013)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 635177655) (.leaf 624018624)) (.branch 116 (.leaf 613075914) (.leaf 602344656))) (.branch 119 (.branch 118 (.leaf 591820108) (.leaf 581497659)) (.branch 120 (.leaf 571372818) (.leaf 561441216)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 922).prefactor = (253312009309309/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 922).cutoff/(generalMeanRows 922).c)).2 =
    (847897450111/3125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 922).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 922).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 922).q*(generalMeanRows 922).c/2-2 = (253/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable141.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 922).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 922

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 922).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 922).criticalRate j.val*(generalMeanRows 922).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 922).c*(generalMeanRows 922).criticalPoint j.val)).2-
      (generalMeanRows 922).J/2-(generalMeanRows 922).error (generalMeanGrid j.val)+
      (generalMeanRows 922).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 922).c)).2-
      (generalMeanRows 922).J/2-(generalMeanRows 922).error 4 := by
  have he : (generalMeanRows 922).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 922) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 922)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0922

/-! Kernel-checked entropy margins for general spectral rectangle 923. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0923
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7284066517) (.branch 2 (.leaf 7071116248) (.leaf 6866468700))) (.branch 5 (.branch 4 (.leaf 6669694947) (.leaf 6480395449)) (.branch 6 (.leaf 6298197409) (.leaf 6122752423)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5953734399) (.leaf 5790837688)) (.branch 10 (.leaf 5633775430) (.leaf 5482278056))) (.branch 13 (.branch 12 (.leaf 5336091946) (.leaf 5194978219)) (.branch 14 (.leaf 5058711639) (.leaf 4927079620))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4799881325) (.branch 17 (.leaf 4676926847) (.leaf 4558036459))) (.branch 20 (.branch 19 (.leaf 4443039926) (.leaf 4331775885)) (.branch 21 (.leaf 4224091262) (.leaf 4119840747)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4018886306) (.leaf 3921096733)) (.branch 25 (.leaf 3826347232) (.leaf 3734519037))) (.branch 28 (.branch 27 (.leaf 3645499052) (.leaf 3559179526)) (.branch 29 (.leaf 3475457742) (.leaf 3394235735)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3315420027) (.branch 32 (.leaf 3238921378) (.leaf 3164654555))) (.branch 35 (.branch 34 (.leaf 3092538118) (.leaf 3022494219)) (.branch 36 (.leaf 2954448410) (.leaf 2888329470)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2824069235) (.leaf 2761602448)) (.branch 40 (.leaf 2700866606) (.leaf 2641801829))) (.branch 43 (.branch 42 (.leaf 2584350726) (.leaf 2528458275)) (.branch 44 (.leaf 2474071708) (.leaf 2421140404))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2369615785) (.branch 47 (.leaf 2319451219) (.leaf 2270601931))) (.branch 50 (.branch 49 (.leaf 2223024917) (.leaf 2176678860)) (.branch 51 (.leaf 2131524055) (.leaf 2087522334)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2044637001) (.leaf 2002832760)) (.branch 55 (.leaf 1962075657) (.leaf 1922333021))) (.branch 58 (.branch 57 (.leaf 1883573407) (.leaf 1845766542)) (.branch 59 (.leaf 1808883274) (.leaf 1772895528))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1737776254) (.branch 62 (.leaf 1703499388) (.leaf 1670039810))) (.branch 65 (.branch 64 (.leaf 1637373303) (.leaf 1605476514)) (.branch 66 (.leaf 1574326925) (.leaf 1543902810)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1514183208) (.leaf 1485147892)) (.branch 70 (.leaf 1456777336) (.leaf 1429052690))) (.branch 73 (.branch 72 (.leaf 1401955751) (.leaf 1375468939)) (.branch 74 (.leaf 1349575270) (.leaf 1324258335))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1299502276) (.branch 77 (.leaf 1275291765) (.leaf 1251611983))) (.branch 80 (.branch 79 (.leaf 1228448602) (.leaf 1205787763)) (.branch 81 (.leaf 1183616062) (.leaf 1161920528)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1140688613) (.leaf 1119908169)) (.branch 85 (.leaf 1099567438) (.leaf 1079655036))) (.branch 88 (.branch 87 (.leaf 1060159938) (.leaf 1041071467)) (.branch 89 (.leaf 1022379280) (.leaf 1004073354)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 986143978) (.branch 92 (.leaf 968581738) (.leaf 951377509))) (.branch 95 (.branch 94 (.leaf 934522444) (.leaf 918007964)) (.branch 96 (.leaf 901825746) (.leaf 885967719)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 870426049) (.leaf 855193138)) (.branch 100 (.leaf 840261608) (.leaf 825624299))) (.branch 103 (.branch 102 (.leaf 811274259) (.leaf 797204736)) (.branch 104 (.leaf 783409174) (.leaf 769881206))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 756614642) (.leaf 743603472)) (.branch 108 (.leaf 730841852) (.leaf 718324104))) (.branch 111 (.branch 110 (.leaf 706044706) (.leaf 693998290)) (.branch 112 (.leaf 682179637) (.leaf 670583668)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 659205446) (.leaf 648040165)) (.branch 116 (.leaf 637083149) (.leaf 626329849))) (.branch 119 (.branch 118 (.leaf 615775835) (.leaf 605416796)) (.branch 120 (.leaf 595248534) (.leaf 585266960)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 923).prefactor = (4956911083580547/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 923).cutoff/(generalMeanRows 923).c)).2 =
    (147599810121/500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 923).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 923).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 923).q*(generalMeanRows 923).c/2-2 = (309/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable256.value]
    have hcontinuation : (generalMeanRows 923).q*(generalMeanRows 923).cutoff/2-2 = (223/147:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable111.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 923).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 923

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 923).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 923).criticalRate j.val*(generalMeanRows 923).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 923).c*(generalMeanRows 923).criticalPoint j.val)).2-
      (generalMeanRows 923).J/2-(generalMeanRows 923).error (generalMeanGrid j.val)+
      (generalMeanRows 923).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 923).c)).2-
      (generalMeanRows 923).J/2-(generalMeanRows 923).error 4 := by
  have he : (generalMeanRows 923).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 923) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 923)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0923

/-! Kernel-checked entropy margins for general spectral rectangle 924. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0924
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7095204000) (.branch 2 (.leaf 6891642976) (.leaf 6696084835))) (.branch 5 (.branch 4 (.leaf 6508111121) (.leaf 6327332106)) (.branch 6 (.leaf 6153384211) (.leaf 5985927732)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5824644806) (.leaf 5669237602)) (.branch 10 (.leaf 5519426697) (.leaf 5374949621))) (.branch 13 (.branch 12 (.leaf 5235559546) (.leaf 5101024100)) (.branch 14 (.leaf 4971124299) (.leaf 4845653571))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4724416878) (.branch 17 (.leaf 4607229906) (.leaf 4493918335))) (.branch 20 (.branch 19 (.leaf 4384317162) (.leaf 4278270087)) (.branch 21 (.leaf 4175628948) (.leaf 4076253200)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3980009436) (.leaf 3886770942)) (.branch 25 (.leaf 3796417294) (.leaf 3708833975))) (.branch 28 (.branch 27 (.leaf 3623912026) (.leaf 3541547721)) (.branch 29 (.leaf 3461642265) (.leaf 3384101513)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3308835708) (.branch 32 (.leaf 3235759238) (.leaf 3164790405))) (.branch 35 (.branch 34 (.leaf 3095851218) (.leaf 3028867189)) (.branch 36 (.leaf 2963767149) (.leaf 2900483072)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2838949914) (.leaf 2779105456)) (.branch 40 (.leaf 2720890164) (.leaf 2664247048))) (.branch 43 (.branch 42 (.leaf 2609121541) (.leaf 2555461372)) (.branch 44 (.leaf 2503216459) (.leaf 2452338796))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2402782359) (.branch 47 (.leaf 2354503007) (.leaf 2307458392))) (.branch 50 (.branch 49 (.leaf 2261607877) (.leaf 2216912454)) (.branch 51 (.leaf 2173334669) (.leaf 2130838546)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2089389528) (.leaf 2048954403)) (.branch 55 (.leaf 2009501250) (.leaf 1970999377))) (.branch 58 (.branch 57 (.leaf 1933419266) (.leaf 1896732525)) (.branch 59 (.leaf 1860911834) (.leaf 1825930899))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1791764410) (.branch 62 (.leaf 1758387993) (.leaf 1725778176))) (.branch 65 (.branch 64 (.leaf 1693912347) (.leaf 1662768716)) (.branch 66 (.leaf 1632326284) (.leaf 1602564806)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1573464763) (.leaf 1545007328)) (.branch 70 (.leaf 1517174341) (.leaf 1489948280))) (.branch 73 (.branch 72 (.leaf 1463312233) (.leaf 1437249876)) (.branch 74 (.leaf 1411745449) (.leaf 1386783730))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1362350017) (.branch 77 (.leaf 1338430108) (.leaf 1315010275))) (.branch 80 (.branch 79 (.leaf 1292077252) (.leaf 1269618215)) (.branch 81 (.leaf 1247620761) (.leaf 1226072897)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1204963022) (.leaf 1184279909)) (.branch 85 (.leaf 1164012694) (.leaf 1144150864))) (.branch 88 (.branch 87 (.leaf 1124684237) (.leaf 1105602957)) (.branch 89 (.leaf 1086897475) (.leaf 1068558543)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1050577200) (.branch 92 (.leaf 1032944761) (.leaf 1015652809))) (.branch 95 (.branch 94 (.leaf 998693182) (.leaf 982057968)) (.branch 96 (.leaf 965739490) (.leaf 949730304)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 934023186) (.leaf 918611126)) (.branch 100 (.leaf 903487319) (.leaf 888645160))) (.branch 103 (.branch 102 (.leaf 874078235) (.leaf 859780315)) (.branch 104 (.leaf 845745349) (.leaf 831967459))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 818440933) (.leaf 805160218)) (.branch 108 (.leaf 792119919) (.leaf 779314787))) (.branch 111 (.branch 110 (.leaf 766739722) (.leaf 754389760)) (.branch 112 (.leaf 742260073) (.leaf 730345966)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 718642866) (.leaf 707146326)) (.branch 116 (.leaf 695852014) (.leaf 684755714))) (.branch 119 (.branch 118 (.leaf 673853319) (.leaf 663140831)) (.branch 120 (.leaf 652614353) (.leaf 642270090)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 924).prefactor = (966833045611653/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 924).cutoff/(generalMeanRows 924).c)).2 =
    (20327060927601/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 924).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 924).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 924).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 924

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 924).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 924).criticalRate j.val*(generalMeanRows 924).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 924).c*(generalMeanRows 924).criticalPoint j.val)).2-
      (generalMeanRows 924).J/2-(generalMeanRows 924).error (generalMeanGrid j.val)+
      (generalMeanRows 924).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 924).c)).2-
      (generalMeanRows 924).J/2-(generalMeanRows 924).error 4 := by
  have he : (generalMeanRows 924).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 924) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 924)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0924

/-! Kernel-checked entropy margins for general spectral rectangle 925. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0925
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6590417592) (.branch 2 (.leaf 6388639075) (.leaf 6194940028))) (.branch 5 (.branch 4 (.leaf 6008897726) (.leaf 5830118378)) (.branch 6 (.leaf 5658234551) (.leaf 5492902873)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5333802003) (.leaf 5180630803)) (.branch 10 (.leaf 5033106714) (.leaf 4890964283))) (.branch 13 (.branch 12 (.leaf 4753953855) (.leaf 4621840369)) (.branch 14 (.leaf 4494402289) (.leaf 4371430619))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4252728014) (.branch 17 (.leaf 4138107971) (.leaf 4027394084))) (.branch 20 (.branch 19 (.leaf 3920419370) (.leaf 3817025641)) (.branch 21 (.leaf 3717062940) (.leaf 3620389012)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3526868819) (.leaf 3436374096)) (.branch 25 (.leaf 3348782936) (.leaf 3263979410))) (.branch 28 (.branch 27 (.leaf 3181853209) (.leaf 3102299320)) (.branch 29 (.leaf 3025217718) (.leaf 2950513081)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2878094529) (.branch 32 (.leaf 2807875373) (.leaf 2739772886))) (.branch 35 (.branch 34 (.leaf 2673708091) (.leaf 2609605555)) (.branch 36 (.leaf 2547393205) (.leaf 2487002146)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2428366503) (.leaf 2371423257)) (.branch 40 (.leaf 2316112107) (.leaf 2262375327))) (.branch 43 (.branch 42 (.leaf 2210157642) (.leaf 2159406100)) (.branch 44 (.leaf 2110069965) (.leaf 2062100603))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2015451383) (.branch 47 (.leaf 1970077581) (.leaf 1925936290))) (.branch 50 (.branch 49 (.leaf 1882986330) (.leaf 1841188174)) (.branch 51 (.leaf 1800503863) (.leaf 1760896941)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1722332382) (.leaf 1684776526)) (.branch 55 (.leaf 1648197016) (.leaf 1612562742))) (.branch 58 (.branch 57 (.leaf 1577843784) (.leaf 1544011357)) (.branch 59 (.leaf 1511037766) (.leaf 1478896355))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1447561462) (.branch 62 (.leaf 1417008376) (.leaf 1387213297))) (.branch 65 (.branch 64 (.leaf 1358153297) (.leaf 1329806284)) (.branch 66 (.leaf 1302150963) (.leaf 1275166806)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1248834021) (.leaf 1223133516)) (.branch 70 (.leaf 1198046877) (.leaf 1173556335))) (.branch 73 (.branch 72 (.leaf 1149644741) (.leaf 1126295544)) (.branch 74 (.leaf 1103492761) (.leaf 1081220961))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1059465235) (.branch 77 (.leaf 1038211184) (.leaf 1017444891))) (.branch 80 (.branch 79 (.leaf 997152909) (.leaf 977322236)) (.branch 81 (.leaf 957940302) (.leaf 938994952)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 920474429) (.leaf 902367357)) (.branch 85 (.leaf 884662730) (.leaf 867349897))) (.branch 88 (.branch 87 (.leaf 850418545) (.leaf 833858693)) (.branch 89 (.leaf 817660674) (.leaf 801815123)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 786312972) (.branch 92 (.leaf 771145433) (.leaf 756303988))) (.branch 95 (.branch 94 (.leaf 741780385) (.leaf 727566621)) (.branch 96 (.leaf 713654937) (.leaf 700037809)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 686707939) (.leaf 673658246)) (.branch 100 (.leaf 660881862) (.leaf 648372120))) (.branch 103 (.branch 102 (.leaf 636122548) (.leaf 624126865)) (.branch 104 (.leaf 612378971) (.leaf 600872944))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 589603029) (.leaf 578563638)) (.branch 108 (.leaf 567749341) (.leaf 557154861))) (.branch 111 (.branch 110 (.leaf 546775070) (.leaf 536604982)) (.branch 112 (.leaf 526639749) (.leaf 516874660)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 507305130) (.leaf 497926700)) (.branch 116 (.leaf 488735034) (.leaf 479725911))) (.branch 119 (.branch 118 (.leaf 470895224) (.leaf 462238976)) (.branch 120 (.leaf 453753276) (.leaf 445434336)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 925).prefactor = (304595204299501/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 925).cutoff/(generalMeanRows 925).c)).2 =
    (149309663161763/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 925).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 925).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 925).q*(generalMeanRows 925).c/2-2 = (1101/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable185.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 925).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 925

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 925).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 925).criticalRate j.val*(generalMeanRows 925).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 925).c*(generalMeanRows 925).criticalPoint j.val)).2-
      (generalMeanRows 925).J/2-(generalMeanRows 925).error (generalMeanGrid j.val)+
      (generalMeanRows 925).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 925).c)).2-
      (generalMeanRows 925).J/2-(generalMeanRows 925).error 4 := by
  have he : (generalMeanRows 925).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 925) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 925)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0925

/-! Kernel-checked entropy margins for general spectral rectangle 926. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0926
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6454992444) (.branch 2 (.leaf 6263266869) (.leaf 6079257073))) (.branch 5 (.branch 4 (.leaf 5902553545) (.leaf 5732774940)) (.branch 6 (.leaf 5569565582) (.leaf 5412593242)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5261547162) (.leaf 5116136286)) (.branch 10 (.leaf 4976087676) (.leaf 4841145083))) (.branch 13 (.branch 12 (.leaf 4711067668) (.leaf 4585628836)) (.branch 14 (.leaf 4464615185) (.leaf 4347825550))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4235070134) (.branch 17 (.leaf 4126169715) (.leaf 4020954919))) (.branch 20 (.branch 19 (.leaf 3919265559) (.leaf 3820950025)) (.branch 21 (.leaf 3725864725) (.leaf 3633873570)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3544847498) (.leaf 3458664039)) (.branch 25 (.leaf 3375206909) (.leaf 3294365633))) (.branch 28 (.branch 27 (.leaf 3216035200) (.leaf 3140115740)) (.branch 29 (.leaf 3066512224) (.leaf 2995134182)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2925895451) (.branch 32 (.leaf 2858713924) (.leaf 2793511330))) (.branch 35 (.branch 34 (.leaf 2730213021) (.leaf 2668747773)) (.branch 36 (.leaf 2609047605) (.leaf 2551047602)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2494685755) (.leaf 2439902808)) (.branch 40 (.leaf 2386642114) (.leaf 2334849504))) (.branch 43 (.branch 42 (.leaf 2284473157) (.leaf 2235463483)) (.branch 44 (.leaf 2187773010) (.leaf 2141356282))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2096169752) (.branch 47 (.leaf 2052171698) (.leaf 2009322127))) (.branch 50 (.branch 49 (.leaf 1967582694) (.leaf 1926916623)) (.branch 51 (.leaf 1887288634) (.leaf 1848664868)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1811012826) (.leaf 1774301300)) (.branch 55 (.leaf 1738500317) (.leaf 1703581081))) (.branch 58 (.branch 57 (.leaf 1669515920) (.leaf 1636278232)) (.branch 59 (.leaf 1603842440) (.leaf 1572183945))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1541279083) (.branch 62 (.leaf 1511105080) (.leaf 1481640020))) (.branch 65 (.branch 64 (.leaf 1452862798) (.leaf 1424753093)) (.branch 66 (.leaf 1397291330) (.leaf 1370458648)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1344236869) (.leaf 1318608473)) (.branch 70 (.leaf 1293556564) (.leaf 1269064847))) (.branch 73 (.branch 72 (.leaf 1245117605) (.leaf 1221699670)) (.branch 74 (.leaf 1198796403) (.leaf 1176393674))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1154477836) (.branch 77 (.leaf 1133035710) (.leaf 1112054565))) (.branch 80 (.branch 79 (.leaf 1091522099) (.leaf 1071426420)) (.branch 81 (.leaf 1051756035) (.leaf 1032499828)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1013647050) (.leaf 995187303)) (.branch 85 (.leaf 977110522) (.leaf 959406971))) (.branch 88 (.branch 87 (.leaf 942067222) (.leaf 925082148)) (.branch 89 (.leaf 908442908) (.leaf 892140940)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 876167947) (.branch 92 (.leaf 860515890) (.leaf 845176974))) (.branch 95 (.branch 94 (.leaf 830143644) (.leaf 815408575)) (.branch 96 (.leaf 800964658) (.leaf 786805001)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 772922914) (.leaf 759311904)) (.branch 100 (.leaf 745965670) (.leaf 732878092))) (.branch 103 (.branch 102 (.leaf 720043229) (.leaf 707455310)) (.branch 104 (.leaf 695108725) (.leaf 682998029))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 671117924) (.leaf 659463264)) (.branch 108 (.leaf 648029044) (.leaf 636810398))) (.branch 111 (.branch 110 (.leaf 625802593) (.leaf 615001022)) (.branch 112 (.leaf 604401207) (.leaf 593998787)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 583789517) (.leaf 573769268)) (.branch 116 (.leaf 563934014) (.leaf 554279840))) (.branch 119 (.branch 118 (.leaf 544802929) (.leaf 535499563)) (.branch 120 (.leaf 526366121) (.leaf 517399072)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 926).prefactor = (4724840282387099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 926).cutoff/(generalMeanRows 926).c)).2 =
    (336207643969377/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 926).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 926).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 926).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 926

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 926).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 926).criticalRate j.val*(generalMeanRows 926).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 926).c*(generalMeanRows 926).criticalPoint j.val)).2-
      (generalMeanRows 926).J/2-(generalMeanRows 926).error (generalMeanGrid j.val)+
      (generalMeanRows 926).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 926).c)).2-
      (generalMeanRows 926).J/2-(generalMeanRows 926).error 4 := by
  have he : (generalMeanRows 926).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 926) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 926)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0926

/-! Kernel-checked entropy margins for general spectral rectangle 927. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0927
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6117250695) (.branch 2 (.leaf 5928148846) (.leaf 5746766929))) (.branch 5 (.branch 4 (.leaf 5572693790) (.leaf 5405546538)) (.branch 6 (.leaf 5244968045) (.leaf 5090624733)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4942204583) (.leaf 4799415372)) (.branch 10 (.leaf 4661983080) (.leaf 4529650461))) (.branch 13 (.branch 12 (.leaf 4402175757) (.leaf 4279331528)) (.branch 14 (.leaf 4160903599) (.leaf 4046690097))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3936500581) (.branch 17 (.leaf 3830155241) (.leaf 3727484172))) (.branch 20 (.branch 19 (.leaf 3628326705) (.leaf 3532530798)) (.branch 21 (.leaf 3439952467) (.leaf 3350455274)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3263909847) (.leaf 3180193441)) (.branch 25 (.leaf 3099189526) (.leaf 3020787414))) (.branch 28 (.branch 27 (.leaf 2944881908) (.leaf 2871372976)) (.branch 29 (.leaf 2800165449) (.leaf 2731168745)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2664296598) (.branch 32 (.leaf 2599466824) (.leaf 2536601089))) (.branch 35 (.branch 34 (.leaf 2475624693) (.leaf 2416466380)) (.branch 36 (.leaf 2359058142) (.leaf 2303335052)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2249235099) (.leaf 2196699031)) (.branch 40 (.leaf 2145670217) (.leaf 2096094507))) (.branch 43 (.branch 42 (.leaf 2047920108) (.leaf 2001097462)) (.branch 44 (.leaf 1955579135) (.leaf 1911319712))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1868275692) (.branch 47 (.leaf 1826405402) (.leaf 1785668899))) (.branch 50 (.branch 49 (.leaf 1746027894) (.leaf 1707445666)) (.branch 51 (.leaf 1669886993) (.leaf 1633318074)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1597706471) (.leaf 1563021036)) (.branch 55 (.leaf 1529231858) (.leaf 1496310202))) (.branch 58 (.branch 57 (.leaf 1464228459) (.leaf 1432960088)) (.branch 59 (.leaf 1402479576) (.leaf 1372762385))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1343784912) (.branch 62 (.leaf 1315524446) (.leaf 1287959129))) (.branch 65 (.branch 64 (.leaf 1261067919) (.leaf 1234830554)) (.branch 66 (.leaf 1209227517) (.leaf 1184240008)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1159849906) (.leaf 1136039747)) (.branch 70 (.leaf 1112792693) (.leaf 1090092506))) (.branch 73 (.branch 72 (.leaf 1067923523) (.leaf 1046270631)) (.branch 74 (.leaf 1025119246) (.leaf 1004455290))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 984265170) (.branch 77 (.leaf 964535759) (.leaf 945254379))) (.branch 80 (.branch 79 (.leaf 926408777) (.leaf 907987114)) (.branch 81 (.leaf 889977946) (.leaf 872370209)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 855153201) (.leaf 838316574)) (.branch 85 (.leaf 821850313) (.leaf 805744729))) (.branch 88 (.branch 87 (.leaf 789990444) (.leaf 774578377)) (.branch 89 (.leaf 759499736) (.leaf 744746007)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 730308941) (.branch 92 (.leaf 716180545) (.leaf 702353072))) (.branch 95 (.branch 94 (.leaf 688819016) (.leaf 675571096)) (.branch 96 (.leaf 662602254) (.leaf 649905643)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 637474621) (.leaf 625302743)) (.branch 100 (.leaf 613383755) (.leaf 601711586))) (.branch 103 (.branch 102 (.leaf 590280342) (.leaf 579084299)) (.branch 104 (.leaf 568117899) (.leaf 557375741))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 546852579) (.leaf 536543316)) (.branch 108 (.leaf 526442994) (.leaf 516546798))) (.branch 111 (.branch 110 (.leaf 506850044) (.leaf 497348177)) (.branch 112 (.leaf 488036767) (.leaf 478911505)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 469968198) (.leaf 461202766)) (.branch 116 (.leaf 452611238) (.leaf 444189748))) (.branch 119 (.branch 118 (.leaf 435934532) (.leaf 427841926)) (.branch 120 (.leaf 419908361) (.leaf 412130359)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 927).prefactor = (4737518948743339/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 927).cutoff/(generalMeanRows 927).c)).2 =
    (1015789323099/3125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 927).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 927).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 927).q*(generalMeanRows 927).c/2-2 = (353/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable084.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 927).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 927

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 927).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 927).criticalRate j.val*(generalMeanRows 927).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 927).c*(generalMeanRows 927).criticalPoint j.val)).2-
      (generalMeanRows 927).J/2-(generalMeanRows 927).error (generalMeanGrid j.val)+
      (generalMeanRows 927).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 927).c)).2-
      (generalMeanRows 927).J/2-(generalMeanRows 927).error 4 := by
  have he : (generalMeanRows 927).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 927) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 927)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0927

/-! Kernel-checked entropy margins for general spectral rectangle 928. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0928
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5747212036) (.branch 2 (.leaf 5561629980) (.leaf 5383755228))) (.branch 5 (.branch 4 (.leaf 5213175555) (.leaf 5049507056)) (.branch 6 (.leaf 4892391650) (.leaf 4741494861)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4596503842) (.leaf 4457125596)) (.branch 10 (.leaf 4323085394) (.leaf 4194125339))) (.branch 13 (.branch 12 (.leaf 4070003076) (.leaf 3950490625)) (.branch 14 (.leaf 3835373322) (.leaf 3724448854))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3617526388) (.branch 17 (.leaf 3514425765) (.leaf 3414976771))) (.branch 20 (.branch 19 (.leaf 3319018470) (.leaf 3226398583)) (.branch 21 (.leaf 3136972930) (.leaf 3050604904)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2967164992) (.leaf 2886530337)) (.branch 25 (.leaf 2808584322) (.leaf 2733216194))) (.branch 28 (.branch 27 (.leaf 2660320710) (.leaf 2589797814)) (.branch 29 (.leaf 2521552332) (.leaf 2455493686)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2391535638) (.branch 32 (.leaf 2329596039) (.leaf 2269596602))) (.branch 35 (.branch 34 (.leaf 2211462691) (.leaf 2155123116)) (.branch 36 (.leaf 2100509949) (.leaf 2047558350)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1996206401) (.leaf 1946394951)) (.branch 40 (.leaf 1898067474) (.leaf 1851169930))) (.branch 43 (.branch 42 (.leaf 1805650642) (.leaf 1761460170)) (.branch 44 (.leaf 1718551203) (.leaf 1676878449))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1636398537) (.branch 47 (.leaf 1597069921) (.leaf 1558852791))) (.branch 50 (.branch 49 (.leaf 1521708988) (.leaf 1485601925)) (.branch 51 (.leaf 1450496515) (.leaf 1416359092)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1383157350) (.leaf 1350860280)) (.branch 55 (.leaf 1319438105) (.leaf 1288862225))) (.branch 58 (.branch 57 (.leaf 1259105165) (.leaf 1230140521)) (.branch 59 (.leaf 1201942911) (.leaf 1174487932))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1147752114) (.branch 62 (.leaf 1121712878) (.leaf 1096348498))) (.branch 65 (.branch 64 (.leaf 1071638063) (.leaf 1047561440)) (.branch 66 (.leaf 1024099243) (.leaf 1001232798)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 978944114) (.leaf 957215854)) (.branch 70 (.leaf 936031304) (.leaf 915374352))) (.branch 73 (.branch 72 (.leaf 895229460) (.leaf 875581638)) (.branch 74 (.leaf 856416425) (.leaf 837719864))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 819478486) (.branch 77 (.leaf 801679284) (.leaf 784309697))) (.branch 80 (.branch 79 (.leaf 767357594) (.leaf 750811254)) (.branch 81 (.leaf 734659350) (.leaf 718890936)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 703495428) (.leaf 688462592)) (.branch 85 (.leaf 673782531) (.leaf 659445669))) (.branch 88 (.branch 87 (.leaf 645442744) (.leaf 631764790)) (.branch 89 (.leaf 618403128) (.leaf 605349357)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 592595341) (.branch 92 (.leaf 580133200) (.leaf 567955301))) (.branch 95 (.branch 94 (.leaf 556054247) (.leaf 544422872)) (.branch 96 (.leaf 533054226) (.leaf 521941576)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 511078390) (.leaf 500458334)) (.branch 100 (.leaf 490075264) (.leaf 479923219))) (.branch 103 (.branch 102 (.leaf 469996415) (.leaf 460289239)) (.branch 104 (.leaf 450796241) (.leaf 441512132))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 432431773) (.leaf 423550176)) (.branch 108 (.leaf 414862494) (.leaf 406364020))) (.branch 111 (.branch 110 (.leaf 398050177) (.leaf 389916522)) (.branch 112 (.leaf 381958731) (.leaf 374172604)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 366554056) (.leaf 359099115)) (.branch 116 (.leaf 351803917) (.leaf 344664706))) (.branch 119 (.branch 118 (.leaf 337677824) (.leaf 330839715)) (.branch 120 (.leaf 324146916) (.leaf 317596059)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 928).prefactor = (118503049689231/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 928).cutoff/(generalMeanRows 928).c)).2 =
    (311971131728987/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 928).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 928).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 928).q*(generalMeanRows 928).c/2-2 = (3097/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable249.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 928).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 928

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 928).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 928).criticalRate j.val*(generalMeanRows 928).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 928).c*(generalMeanRows 928).criticalPoint j.val)).2-
      (generalMeanRows 928).J/2-(generalMeanRows 928).error (generalMeanGrid j.val)+
      (generalMeanRows 928).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 928).c)).2-
      (generalMeanRows 928).J/2-(generalMeanRows 928).error 4 := by
  have he : (generalMeanRows 928).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 928) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 928)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0928

/-! Kernel-checked entropy margins for general spectral rectangle 929. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0929
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5760121959) (.branch 2 (.leaf 5584680732) (.leaf 5416499015))) (.branch 5 (.branch 4 (.leaf 5255181518) (.leaf 5100360395)) (.branch 6 (.leaf 4951692832) (.leaf 4808858898)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4671559629) (.leaf 4539515310)) (.branch 10 (.leaf 4412463929) (.leaf 4290159795))) (.branch 13 (.branch 12 (.leaf 4172372273) (.leaf 4058884656)) (.branch 14 (.leaf 3949493132) (.leaf 3844005846))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3742242046) (.branch 17 (.leaf 3644031304) (.leaf 3549212805))) (.branch 20 (.branch 19 (.leaf 3457634689) (.leaf 3369153455)) (.branch 21 (.leaf 3283633409) (.leaf 3200946152)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3120970120) (.leaf 3043590144)) (.branch 25 (.leaf 2968697053) (.leaf 2896187305))) (.branch 28 (.branch 27 (.leaf 2825962641) (.leaf 2757929769)) (.branch 29 (.leaf 2692000068) (.leaf 2628089310)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2566117407) (.branch 32 (.leaf 2506008171) (.leaf 2447689091))) (.branch 35 (.branch 34 (.leaf 2391091124) (.leaf 2336148502)) (.branch 36 (.leaf 2282798552) (.leaf 2230981522)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2180640423) (.leaf 2131720883)) (.branch 40 (.leaf 2084171000) (.leaf 2037941217))) (.branch 43 (.branch 42 (.leaf 1992984197) (.leaf 1949254704)) (.branch 44 (.leaf 1906709496) (.leaf 1865307224))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1825008330) (.branch 47 (.leaf 1785774963) (.leaf 1747570887))) (.branch 50 (.branch 49 (.leaf 1710361404) (.leaf 1674113275)) (.branch 51 (.leaf 1638794650) (.leaf 1604375000)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1570825049) (.leaf 1538116719)) (.branch 55 (.leaf 1506223069) (.leaf 1475118241))) (.branch 58 (.branch 57 (.leaf 1444777408) (.leaf 1415176729)) (.branch 59 (.leaf 1386293298) (.leaf 1358105104))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1330590988) (.branch 62 (.leaf 1303730603) (.leaf 1277504380))) (.branch 65 (.branch 64 (.leaf 1251893490) (.leaf 1226879811)) (.branch 66 (.leaf 1202445897) (.leaf 1178574948)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1155250780) (.leaf 1132457800)) (.branch 70 (.leaf 1110180977) (.leaf 1088405822))) (.branch 73 (.branch 72 (.leaf 1067118359) (.leaf 1046305109)) (.branch 74 (.leaf 1025953063) (.leaf 1006049668))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 986582801) (.branch 77 (.leaf 967540757) (.leaf 948912227))) (.branch 80 (.branch 79 (.leaf 930686287) (.leaf 912852374)) (.branch 81 (.leaf 895400280) (.leaf 878320133)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 861602381) (.leaf 845237786)) (.branch 85 (.leaf 829217405) (.leaf 813532583))) (.branch 88 (.branch 87 (.leaf 798174936) (.leaf 783136349)) (.branch 89 (.leaf 768408955) (.leaf 753985136)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 739857504) (.branch 92 (.leaf 726018899) (.leaf 712462377))) (.branch 95 (.branch 94 (.leaf 699181204) (.leaf 686168844)) (.branch 96 (.leaf 673418958) (.leaf 660925391)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 648682168) (.leaf 636683487)) (.branch 100 (.leaf 624923712) (.leaf 613397369))) (.branch 103 (.branch 102 (.leaf 602099139) (.leaf 591023851)) (.branch 104 (.leaf 580166478) (.leaf 569522135))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 559086068) (.leaf 548853655)) (.branch 108 (.leaf 538820397) (.leaf 528981919))) (.branch 111 (.branch 110 (.leaf 519333960) (.leaf 509872373)) (.branch 112 (.leaf 500593121) (.leaf 491492273)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 482565998) (.leaf 473810565)) (.branch 116 (.leaf 465222338) (.leaf 456797776))) (.branch 119 (.branch 118 (.leaf 448533425) (.leaf 440425918)) (.branch 120 (.leaf 432471974) (.leaf 424668390)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 929).prefactor = (4564032513349231/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 929).cutoff/(generalMeanRows 929).c)).2 =
    (182818931753379/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 929).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 929).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 929).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 929

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 929).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 929).criticalRate j.val*(generalMeanRows 929).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 929).c*(generalMeanRows 929).criticalPoint j.val)).2-
      (generalMeanRows 929).J/2-(generalMeanRows 929).error (generalMeanGrid j.val)+
      (generalMeanRows 929).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 929).c)).2-
      (generalMeanRows 929).J/2-(generalMeanRows 929).error 4 := by
  have he : (generalMeanRows 929).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 929) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 929)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0929

/-! Kernel-checked entropy margins for general spectral rectangle 930. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0930
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5530091439) (.branch 2 (.leaf 5358114573) (.leaf 5193327403))) (.branch 5 (.branch 4 (.leaf 5035336108) (.leaf 4883774277)) (.branch 6 (.leaf 4738300499) (.leaf 4598596229)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4464363865) (.leaf 4335325042)) (.branch 10 (.leaf 4211219082) (.leaf 4091801615))) (.branch 13 (.branch 12 (.leaf 3976843315) (.leaf 3866128773)) (.branch 14 (.leaf 3759455458) (.leaf 3656632786))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3557481262) (.branch 17 (.leaf 3461831700) (.leaf 3369524511))) (.branch 20 (.branch 19 (.leaf 3280409045) (.leaf 3194342995)) (.branch 21 (.leaf 3111191841) (.leaf 3030828343)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2953132074) (.leaf 2877988982)) (.branch 25 (.leaf 2805290995) (.leaf 2734935646))) (.branch 28 (.branch 27 (.leaf 2666825733) (.leaf 2600868996)) (.branch 29 (.leaf 2536977825) (.leaf 2475068982)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2415063345) (.branch 32 (.leaf 2356885669) (.leaf 2300464364))) (.branch 35 (.branch 34 (.leaf 2245731285) (.leaf 2192621540)) (.branch 36 (.leaf 2141073306) (.leaf 2091027663)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2042428430) (.leaf 1995222017)) (.branch 40 (.leaf 1949357288) (.leaf 1904785426))) (.branch 43 (.branch 42 (.leaf 1861459813) (.leaf 1819335913)) (.branch 44 (.leaf 1778371161) (.leaf 1738524865))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1699758104) (.branch 47 (.leaf 1662033644) (.leaf 1625315847))) (.branch 50 (.branch 49 (.leaf 1589570594) (.leaf 1554765206)) (.branch 51 (.leaf 1520868376) (.leaf 1487850098)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1455681604) (.leaf 1424335306)) (.branch 55 (.leaf 1393784737) (.leaf 1364004497))) (.branch 58 (.branch 57 (.leaf 1334970203) (.leaf 1306658438)) (.branch 59 (.leaf 1279046712) (.leaf 1252113409))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1225837758) (.branch 62 (.leaf 1200199782) (.leaf 1175180270))) (.branch 65 (.branch 64 (.leaf 1150760739) (.leaf 1126923402)) (.branch 66 (.leaf 1103651133) (.leaf 1080927443)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1058736449) (.leaf 1037062845)) (.branch 70 (.leaf 1015891880) (.leaf 995209333))) (.branch 73 (.branch 72 (.leaf 975001488) (.leaf 955255116)) (.branch 74 (.leaf 935957451) (.leaf 917096170))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 898659376) (.branch 77 (.leaf 880635581) (.leaf 863013685))) (.branch 80 (.branch 79 (.leaf 845782965) (.leaf 828933055)) (.branch 81 (.leaf 812453933) (.leaf 796335909)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 780569607) (.leaf 765145959)) (.branch 85 (.leaf 750056184) (.leaf 735291786))) (.branch 88 (.branch 87 (.leaf 720844535) (.leaf 706706463)) (.branch 89 (.leaf 692869846) (.leaf 679327205)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 666071285) (.branch 92 (.leaf 653095057) (.leaf 640391703))) (.branch 95 (.branch 94 (.leaf 627954609) (.leaf 615777360)) (.branch 96 (.leaf 603853728) (.leaf 592177672)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 580743324) (.leaf 569544986)) (.branch 100 (.leaf 558577126) (.leaf 547834368))) (.branch 103 (.branch 102 (.leaf 537311489) (.leaf 527003412)) (.branch 104 (.leaf 516905202) (.leaf 507012062))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 497319326) (.leaf 487822455)) (.branch 108 (.leaf 478517035) (.leaf 469398769))) (.branch 111 (.branch 110 (.leaf 460463477) (.leaf 451707089)) (.branch 112 (.leaf 443125643) (.leaf 434715281)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 426472245) (.leaf 418392875)) (.branch 116 (.leaf 410473606) (.leaf 402710963))) (.branch 119 (.branch 118 (.leaf 395101559) (.leaf 387642094)) (.branch 120 (.leaf 380329351) (.leaf 373160192)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 930).prefactor = (568485038376999/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 930).cutoff/(generalMeanRows 930).c)).2 =
    (36629554192573/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 930).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 930).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 930).q*(generalMeanRows 930).c/2-2 = (73/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable024.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 930).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 930

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 930).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 930).criticalRate j.val*(generalMeanRows 930).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 930).c*(generalMeanRows 930).criticalPoint j.val)).2-
      (generalMeanRows 930).J/2-(generalMeanRows 930).error (generalMeanGrid j.val)+
      (generalMeanRows 930).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 930).c)).2-
      (generalMeanRows 930).J/2-(generalMeanRows 930).error 4 := by
  have he : (generalMeanRows 930).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 930) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 930)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0930

/-! Kernel-checked entropy margins for general spectral rectangle 931. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0931
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5265009582) (.branch 2 (.leaf 5096994700) (.leaf 4936088970))) (.branch 5 (.branch 4 (.leaf 4781900636) (.leaf 4634065274)) (.branch 6 (.leaf 4492243399) (.leaf 4356118327)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4225394273) (.leaf 4099794635)) (.branch 10 (.leaf 3979060461) (.leaf 3862949065))) (.branch 13 (.branch 12 (.leaf 3751232770) (.leaf 3643697774)) (.branch 14 (.leaf 3540143127) (.leaf 3440379788))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3344229771) (.branch 17 (.leaf 3251525370) (.leaf 3162108441))) (.branch 20 (.branch 19 (.leaf 3075829749) (.leaf 2992548371)) (.branch 21 (.leaf 2912131138) (.leaf 2834452131)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2759392211) (.leaf 2686838585)) (.branch 25 (.leaf 2616684407) (.leaf 2548828406))) (.branch 28 (.branch 27 (.leaf 2483174547) (.leaf 2419631704)) (.branch 29 (.leaf 2358113372) (.leaf 2298537388)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2240825676) (.branch 32 (.leaf 2184904006) (.leaf 2130701776))) (.branch 35 (.branch 34 (.leaf 2078151799) (.leaf 2027190114)) (.branch 36 (.leaf 1977755802) (.leaf 1929790817)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1883239827) (.leaf 1838050067)) (.branch 40 (.leaf 1794171196) (.leaf 1751555171))) (.branch 43 (.branch 42 (.leaf 1710156120) (.leaf 1669930231)) (.branch 44 (.leaf 1630835639) (.leaf 1592832329))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1555882035) (.branch 47 (.leaf 1519948157) (.leaf 1484995669))) (.branch 50 (.branch 49 (.leaf 1450991041) (.leaf 1417902168)) (.branch 51 (.leaf 1385698294) (.leaf 1354349946)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1323828872) (.leaf 1294107981)) (.branch 55 (.leaf 1265161285) (.leaf 1236963848))) (.branch 58 (.branch 57 (.leaf 1209491734) (.leaf 1182721959)) (.branch 59 (.leaf 1156632447) (.leaf 1131201989))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1106410198) (.branch 62 (.leaf 1082237473) (.leaf 1058664966))) (.branch 65 (.branch 64 (.leaf 1035674542) (.leaf 1013248750)) (.branch 66 (.leaf 991370792) (.leaf 970024492)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 949194269) (.leaf 928865111)) (.branch 70 (.leaf 909022550) (.leaf 889652639))) (.branch 73 (.branch 72 (.leaf 870741925) (.leaf 852277435)) (.branch 74 (.leaf 834246649) (.leaf 816637483))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 799438272) (.branch 77 (.leaf 782637749) (.leaf 766225031))) (.branch 80 (.branch 79 (.leaf 750189605) (.leaf 734521306)) (.branch 81 (.leaf 719210310) (.leaf 704247116)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 689622534) (.leaf 675327672)) (.branch 85 (.leaf 661353925) (.leaf 647692965))) (.branch 88 (.branch 87 (.leaf 634336725) (.leaf 621277396)) (.branch 89 (.leaf 608507410) (.leaf 596019436)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 583806368) (.branch 92 (.leaf 571861318) (.leaf 560177607))) (.branch 95 (.branch 94 (.leaf 548748757) (.leaf 537568483)) (.branch 96 (.leaf 526630689) (.leaf 515929456)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 505459042) (.leaf 495213868)) (.branch 100 (.leaf 485188519) (.leaf 475377735))) (.branch 103 (.branch 102 (.leaf 465776404) (.leaf 456379559)) (.branch 104 (.leaf 447182376) (.leaf 438180161))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 429368353) (.leaf 420742515)) (.branch 108 (.leaf 412298334) (.leaf 404031610))) (.branch 111 (.branch 110 (.leaf 395938262) (.leaf 388014314)) (.branch 112 (.leaf 380255898) (.leaf 372659248)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 365220699) (.leaf 357936680)) (.branch 116 (.leaf 350803713) (.leaf 343818411))) (.branch 119 (.branch 118 (.leaf 336977476) (.leaf 330277690)) (.branch 120 (.leaf 323715921) (.leaf 317289114)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 931).prefactor = (452430138540919/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 931).cutoff/(generalMeanRows 931).c)).2 =
    (72958582408239/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 931).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 931).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 931).q*(generalMeanRows 931).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 931).q*(generalMeanRows 931).cutoff/2-2 = (516/259:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable038.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 931).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 931

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 931).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 931).criticalRate j.val*(generalMeanRows 931).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 931).c*(generalMeanRows 931).criticalPoint j.val)).2-
      (generalMeanRows 931).J/2-(generalMeanRows 931).error (generalMeanGrid j.val)+
      (generalMeanRows 931).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 931).c)).2-
      (generalMeanRows 931).J/2-(generalMeanRows 931).error 4 := by
  have he : (generalMeanRows 931).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 931) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 931)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0931

/-! Kernel-checked entropy margins for general spectral rectangle 932. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0932
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5211791842) (.branch 2 (.leaf 5047129542) (.leaf 4889451274))) (.branch 5 (.branch 4 (.leaf 4738368859) (.leaf 4593521355)) (.branch 6 (.leaf 4454572676) (.leaf 4321209457)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4193139161) (.leaf 4070088367)) (.branch 10 (.leaf 3951801236) (.leaf 3838038130))) (.branch 13 (.branch 12 (.leaf 3728574359) (.leaf 3623199051)) (.branch 14 (.leaf 3521714120) (.leaf 3423933332))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3329681449) (.branch 17 (.leaf 3238793455) (.leaf 3151113835))) (.branch 20 (.branch 19 (.leaf 3066495927) (.leaf 2984801321)) (.branch 21 (.leaf 2905899305) (.leaf 2829666357)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2755985678) (.leaf 2684746760)) (.branch 25 (.leaf 2615844983) (.leaf 2549181246))) (.branch 28 (.branch 27 (.leaf 2484661626) (.leaf 2422197057)) (.branch 29 (.leaf 2361703037) (.leaf 2303099352)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2246309820) (.branch 32 (.leaf 2191262054) (.leaf 2137887239))) (.branch 35 (.branch 34 (.leaf 2086119930) (.leaf 2035897850)) (.branch 36 (.leaf 1987161718) (.leaf 1939855076)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1893924133) (.leaf 1849317613)) (.branch 40 (.leaf 1805986625) (.leaf 1763884525))) (.branch 43 (.branch 42 (.leaf 1722966797) (.leaf 1683190942)) (.branch 44 (.leaf 1644516365) (.leaf 1606904279))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1570317608) (.branch 47 (.leaf 1534720897) (.leaf 1500080231))) (.branch 50 (.branch 49 (.leaf 1466363154) (.leaf 1433538594)) (.branch 51 (.leaf 1401576795) (.leaf 1370449250)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1340128637) (.leaf 1310588763)) (.branch 55 (.leaf 1281804507) (.leaf 1253751767))) (.branch 58 (.branch 57 (.leaf 1226407412) (.leaf 1199749236)) (.branch 59 (.leaf 1173755908) (.leaf 1148406939))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1123682636) (.branch 62 (.leaf 1099564064) (.leaf 1076033018))) (.branch 65 (.branch 64 (.leaf 1053071981) (.leaf 1030664095)) (.branch 66 (.leaf 1008793134) (.leaf 987443472)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 966600055) (.leaf 946248381)) (.branch 70 (.leaf 926374467) (.leaf 906964835))) (.branch 73 (.branch 72 (.leaf 888006483) (.leaf 869486868)) (.branch 74 (.leaf 851393885) (.leaf 833715848))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 816441473) (.branch 77 (.leaf 799559859) (.leaf 783060475))) (.branch 80 (.branch 79 (.leaf 766933141) (.leaf 751168018)) (.branch 81 (.leaf 735755588) (.leaf 720686646)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 705952286) (.leaf 691543886)) (.branch 85 (.leaf 677453102) (.leaf 663671852))) (.branch 88 (.branch 87 (.leaf 650192308) (.leaf 637006886)) (.branch 89 (.leaf 624108237) (.leaf 611489236)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 599142976) (.branch 92 (.leaf 587062756) (.leaf 575242079))) (.branch 95 (.branch 94 (.leaf 563674638) (.leaf 552354315)) (.branch 96 (.leaf 541275167) (.leaf 530431427)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 519817494) (.leaf 509427924)) (.branch 100 (.leaf 499257433) (.leaf 489300880))) (.branch 103 (.branch 102 (.leaf 479553273) (.leaf 470009756)) (.branch 104 (.leaf 460665608) (.leaf 451516238))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 442557177) (.leaf 433784081)) (.branch 108 (.leaf 425192720) (.leaf 416778977))) (.branch 111 (.branch 110 (.leaf 408538846) (.leaf 400468424)) (.branch 112 (.leaf 392563913) (.leaf 384821610)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 377237911) (.leaf 369809304)) (.branch 116 (.leaf 362532365) (.leaf 355403758))) (.branch 119 (.branch 118 (.leaf 348420232) (.leaf 341578617)) (.branch 120 (.leaf 334875820) (.leaf 328308828)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 932).prefactor = (898786176584061/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 932).cutoff/(generalMeanRows 932).c)).2 =
    (190914549596881/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 932).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 932).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 932).q*(generalMeanRows 932).c/2-2 = (1529/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable303.value]
    have hcontinuation : (generalMeanRows 932).q*(generalMeanRows 932).cutoff/2-2 = (904/441:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable304.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 932).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 932

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 932).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 932).criticalRate j.val*(generalMeanRows 932).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 932).c*(generalMeanRows 932).criticalPoint j.val)).2-
      (generalMeanRows 932).J/2-(generalMeanRows 932).error (generalMeanGrid j.val)+
      (generalMeanRows 932).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 932).c)).2-
      (generalMeanRows 932).J/2-(generalMeanRows 932).error 4 := by
  have he : (generalMeanRows 932).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 932) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 932)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0932

/-! Kernel-checked entropy margins for general spectral rectangle 933. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0933
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5169785359) (.branch 2 (.leaf 5000156646) (.leaf 4837806981))) (.branch 5 (.branch 4 (.leaf 4682332783) (.leaf 4533358683)) (.branch 6 (.leaf 4390535055) (.leaf 4253535816)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4122056456) (.leaf 3995812280)) (.branch 10 (.leaf 3874536812) (.leaf 3757980374))) (.branch 13 (.branch 12 (.leaf 3645908784) (.leaf 3538102191)) (.branch 14 (.leaf 3434354008) (.leaf 3334469942))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3238267117) (.branch 17 (.leaf 3145573261) (.leaf 3056225974))) (.branch 20 (.branch 19 (.leaf 2970072048) (.leaf 2886966847)) (.branch 21 (.leaf 2806773736) (.leaf 2729363557)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2654614139) (.leaf 2582409857)) (.branch 25 (.leaf 2512641212) (.leaf 2445204452))) (.branch 28 (.branch 27 (.leaf 2380001215) (.leaf 2316938197)) (.branch 29 (.leaf 2255926851) (.leaf 2196883100)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2139727072) (.branch 32 (.leaf 2084382851) (.leaf 2030778254))) (.branch 35 (.branch 34 (.leaf 1978844608) (.leaf 1928516556)) (.branch 36 (.leaf 1879731868) (.leaf 1832431265)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1786558254) (.leaf 1742058980)) (.branch 40 (.leaf 1698882074) (.leaf 1656978527))) (.branch 43 (.branch 42 (.leaf 1616301556) (.leaf 1576806490)) (.branch 44 (.leaf 1538450656) (.leaf 1501193275))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1464995364) (.branch 47 (.leaf 1429819641) (.leaf 1395630441))) (.branch 50 (.branch 49 (.leaf 1362393630) (.leaf 1330076529)) (.branch 51 (.leaf 1298647845) (.leaf 1268077592)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1238337039) (.leaf 1209398636)) (.branch 55 (.leaf 1181235965) (.leaf 1153823683))) (.branch 58 (.branch 57 (.leaf 1127137465) (.leaf 1101153964)) (.branch 59 (.leaf 1075850759) (.leaf 1051206309))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1027199920) (.branch 62 (.leaf 1003811698) (.leaf 981022514))) (.branch 65 (.branch 64 (.leaf 958813970) (.leaf 937168366)) (.branch 66 (.leaf 916068667) (.leaf 895498471)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 875441987) (.leaf 855884001)) (.branch 70 (.leaf 836809855) (.leaf 818205419))) (.branch 73 (.branch 72 (.leaf 800057071) (.leaf 782351675)) (.branch 74 (.leaf 765076558) (.leaf 748219491))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 731768671) (.branch 77 (.leaf 715712703) (.leaf 700040581))) (.branch 80 (.branch 79 (.leaf 684741674) (.leaf 669805711)) (.branch 81 (.leaf 655222762) (.leaf 640983230)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 627077833) (.leaf 613497594)) (.branch 85 (.leaf 600233826) (.leaf 587278124))) (.branch 88 (.branch 87 (.leaf 574622353) (.leaf 562258634)) (.branch 89 (.leaf 550179338) (.leaf 538377077)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 526844689) (.branch 92 (.leaf 515575236) (.leaf 504561993))) (.branch 95 (.branch 94 (.leaf 493798439) (.leaf 483278249)) (.branch 96 (.leaf 472995291) (.leaf 462943614)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 453117444) (.leaf 443511175)) (.branch 100 (.leaf 434119369) (.leaf 424936742))) (.branch 103 (.branch 102 (.leaf 415958166) (.leaf 407178656)) (.branch 104 (.leaf 398593372) (.leaf 390197611))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 381986801) (.leaf 373956499)) (.branch 108 (.leaf 366102385) (.leaf 358420257))) (.branch 111 (.branch 110 (.leaf 350906030) (.leaf 343555732)) (.branch 112 (.leaf 336365494) (.leaf 329331557)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 322450259) (.leaf 315718037)) (.branch 116 (.leaf 309131422) (.leaf 302687038))) (.branch 119 (.branch 118 (.leaf 296381597) (.leaf 290211895)) (.branch 120 (.leaf 284174814) (.leaf 278267314)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 933).prefactor = (926721556204839/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 933).cutoff/(generalMeanRows 933).c)).2 =
    (361256090076047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 933).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 933).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 933).q*(generalMeanRows 933).c/2-2 = (1621/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable288.value]
    have hcontinuation : (generalMeanRows 933).q*(generalMeanRows 933).cutoff/2-2 = (7298/3589:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable305.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 933).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 933

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 933).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 933).criticalRate j.val*(generalMeanRows 933).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 933).c*(generalMeanRows 933).criticalPoint j.val)).2-
      (generalMeanRows 933).J/2-(generalMeanRows 933).error (generalMeanGrid j.val)+
      (generalMeanRows 933).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 933).c)).2-
      (generalMeanRows 933).J/2-(generalMeanRows 933).error 4 := by
  have he : (generalMeanRows 933).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 933) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 933)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0933

/-! Kernel-checked entropy margins for general spectral rectangle 934. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0934
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5084826162) (.branch 2 (.leaf 4913605628) (.leaf 4749792537))) (.branch 5 (.branch 4 (.leaf 4592976612) (.leaf 4442776191)) (.branch 6 (.leaf 4298835734) (.leaf 4160823587)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4028429988) (.leaf 3901365282)) (.branch 10 (.leaf 3779358309) (.leaf 3662154956))) (.branch 13 (.branch 12 (.leaf 3549516843) (.leaf 3441220140)) (.branch 14 (.leaf 3337054482) (.leaf 3236821993))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3140336390) (.branch 17 (.leaf 3047422162) (.leaf 2957913826))) (.branch 20 (.branch 19 (.leaf 2871655239) (.leaf 2788498971)) (.branch 21 (.leaf 2708305720) (.leaf 2630943787)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2556288576) (.leaf 2484222145)) (.branch 25 (.leaf 2414632787) (.leaf 2347414634))) (.branch 28 (.branch 27 (.leaf 2282467306) (.leaf 2219695571)) (.branch 29 (.leaf 2159009034) (.leaf 2100321851)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2043552460) (.branch 32 (.leaf 1988623330) (.leaf 1935460726))) (.branch 35 (.branch 34 (.leaf 1883994495) (.leaf 1834157858)) (.branch 36 (.leaf 1785887225) (.leaf 1739122012)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1693804480) (.leaf 1649879575)) (.branch 40 (.leaf 1607294783) (.leaf 1565999993))) (.branch 43 (.branch 42 (.leaf 1525947371) (.leaf 1487091233)) (.branch 44 (.leaf 1449387940) (.leaf 1412795785))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1377274893) (.branch 47 (.leaf 1342787131) (.leaf 1309296015))) (.branch 50 (.branch 49 (.leaf 1276766629) (.leaf 1245165542)) (.branch 51 (.leaf 1214460740) (.leaf 1184621549)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1155618575) (.leaf 1127423636)) (.branch 55 (.leaf 1100009706) (.leaf 1073350860))) (.branch 58 (.branch 57 (.leaf 1047422219) (.leaf 1022199902)) (.branch 59 (.leaf 997660975) (.leaf 973783412))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 950546049) (.branch 62 (.leaf 927928546) (.leaf 905911347))) (.branch 65 (.branch 64 (.leaf 884475644) (.leaf 863603347)) (.branch 66 (.leaf 843277046) (.leaf 823479984)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 804196027) (.leaf 785409638)) (.branch 70 (.leaf 767105847) (.leaf 749270229))) (.branch 73 (.branch 72 (.leaf 731888881) (.leaf 714948397)) (.branch 74 (.leaf 698435848) (.leaf 682338763))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 666645105) (.branch 77 (.leaf 651343261) (.leaf 636422015))) (.branch 80 (.branch 79 (.leaf 621870539) (.leaf 607678371)) (.branch 81 (.leaf 593835405) (.leaf 580331875)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 567158339) (.leaf 554305669)) (.branch 85 (.leaf 541765037) (.leaf 529527903))) (.branch 88 (.branch 87 (.leaf 517586005) (.leaf 505931346)) (.branch 89 (.leaf 494556187) (.leaf 483453032)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 472614626) (.branch 92 (.leaf 462033937) (.leaf 451704156))) (.branch 95 (.branch 94 (.leaf 441618683) (.leaf 431771120)) (.branch 96 (.leaf 422155268) (.leaf 412765113)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 403594824) (.leaf 394638746)) (.branch 100 (.leaf 385891389) (.leaf 377347430))) (.branch 103 (.branch 102 (.leaf 369001700) (.leaf 360849183)) (.branch 104 (.leaf 352885007) (.leaf 345104443))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 337502896) (.leaf 330075906)) (.branch 108 (.leaf 322819135) (.leaf 315728372))) (.branch 111 (.branch 110 (.leaf 308799521) (.leaf 302028604)) (.branch 112 (.leaf 295411751) (.leaf 288945200)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 282625293) (.leaf 276448472)) (.branch 116 (.leaf 270411275) (.leaf 264510336))) (.branch 119 (.branch 118 (.leaf 258742377) (.leaf 253104211)) (.branch 120 (.leaf 247592734) (.leaf 242204926)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 934).prefactor = (4701927814794019/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 934).cutoff/(generalMeanRows 934).c)).2 =
    (347650438020269/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 934).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 934).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 934).q*(generalMeanRows 934).c/2-2 = (849/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable306.value]
    have hcontinuation : (generalMeanRows 934).q*(generalMeanRows 934).cutoff/2-2 = (7298/3589:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable305.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 934).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 934

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 934).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 934).criticalRate j.val*(generalMeanRows 934).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 934).c*(generalMeanRows 934).criticalPoint j.val)).2-
      (generalMeanRows 934).J/2-(generalMeanRows 934).error (generalMeanGrid j.val)+
      (generalMeanRows 934).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 934).c)).2-
      (generalMeanRows 934).J/2-(generalMeanRows 934).error 4 := by
  have he : (generalMeanRows 934).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 934) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 934)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0934

/-! Kernel-checked entropy margins for general spectral rectangle 935. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0935
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5288153809) (.branch 2 (.leaf 5121078914) (.leaf 4961090381))) (.branch 5 (.branch 4 (.leaf 4807794342) (.leaf 4660824566)) (.branch 6 (.leaf 4519840043) (.leaf 4384522817)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4254576065) (.leaf 4129722359)) (.branch 10 (.leaf 4009702112) (.leaf 3894272175))) (.branch 13 (.branch 12 (.leaf 3783204567) (.leaf 3676285325)) (.branch 14 (.leaf 3573313460) (.leaf 3474100010))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3378467171) (.branch 17 (.leaf 3286247506) (.leaf 3197283224))) (.branch 20 (.branch 19 (.leaf 3111425515) (.leaf 3028533939)) (.branch 21 (.leaf 2948475868) (.leaf 2871125973)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2796365742) (.leaf 2724083048)) (.branch 25 (.leaf 2654171738) (.leaf 2586531259))) (.branch 28 (.branch 27 (.leaf 2521066312) (.leaf 2457686527)) (.branch 29 (.leaf 2396306163) (.leaf 2336843830)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2279222231) (.branch 32 (.leaf 2223367918) (.leaf 2169211068))) (.branch 35 (.branch 34 (.leaf 2116685276) (.leaf 2065727354)) (.branch 36 (.leaf 2016277151) (.leaf 1968277384)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1921673470) (.leaf 1876413387)) (.branch 40 (.leaf 1832447523) (.leaf 1789728552))) (.branch 43 (.branch 42 (.leaf 1748211308) (.leaf 1707852666)) (.branch 44 (.leaf 1668611438) (.leaf 1630448268))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1593325538) (.branch 47 (.leaf 1557207272) (.leaf 1522059059))) (.branch 50 (.branch 49 (.leaf 1487847967) (.leaf 1454542470)) (.branch 51 (.leaf 1422112374) (.leaf 1390528755)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1359763891) (.leaf 1329791206)) (.branch 55 (.leaf 1300585209) (.leaf 1272121447))) (.branch 58 (.branch 57 (.leaf 1244376450) (.leaf 1217327684)) (.branch 59 (.leaf 1190953508) (.leaf 1165233132))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1140146573) (.branch 62 (.leaf 1115674622) (.leaf 1091798805))) (.branch 65 (.branch 64 (.leaf 1068501347) (.leaf 1045765147)) (.branch 66 (.leaf 1023573738) (.leaf 1001911265)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 980762456) (.leaf 960112593)) (.branch 70 (.leaf 939947491) (.leaf 920253474))) (.branch 73 (.branch 72 (.leaf 901017348) (.leaf 882226388)) (.branch 74 (.leaf 863868311) (.leaf 845931260))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 828403784) (.branch 77 (.leaf 811274825) (.leaf 794533696))) (.branch 80 (.branch 79 (.leaf 778170068) (.leaf 762173958)) (.branch 81 (.leaf 746535708) (.leaf 731245980)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 716295735) (.leaf 701676227)) (.branch 85 (.leaf 687378988) (.leaf 673395818))) (.branch 88 (.branch 87 (.leaf 659718775) (.leaf 646340163)) (.branch 89 (.leaf 633252526) (.leaf 620448635)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 607921480) (.branch 92 (.leaf 595664264) (.leaf 583670393))) (.branch 95 (.branch 94 (.leaf 571933469) (.leaf 560447282)) (.branch 96 (.leaf 549205805) (.leaf 538203186)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 527433739) (.leaf 516891944)) (.branch 100 (.leaf 506572437) (.leaf 496470003))) (.branch 103 (.branch 102 (.leaf 486579577) (.leaf 476896230)) (.branch 104 (.leaf 467415174) (.leaf 458131749))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 449041422) (.leaf 440139785)) (.branch 108 (.leaf 431422545) (.leaf 422885526))) (.branch 111 (.branch 110 (.leaf 414524662) (.leaf 406335995)) (.branch 112 (.leaf 398315668) (.leaf 390459927)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 382765114) (.leaf 375227664)) (.branch 116 (.leaf 367844105) (.leaf 360611052))) (.branch 119 (.branch 118 (.leaf 353525205) (.leaf 346583347)) (.branch 120 (.leaf 339782343) (.leaf 333119132)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 935).prefactor = (4559774917200131/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 935).cutoff/(generalMeanRows 935).c)).2 =
    (190914549596881/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 935).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 935).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 935).q*(generalMeanRows 935).c/2-2 = (1529/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable303.value]
    have hcontinuation : (generalMeanRows 935).q*(generalMeanRows 935).cutoff/2-2 = (904/441:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable304.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 935).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 935

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 935).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 935).criticalRate j.val*(generalMeanRows 935).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 935).c*(generalMeanRows 935).criticalPoint j.val)).2-
      (generalMeanRows 935).J/2-(generalMeanRows 935).error (generalMeanGrid j.val)+
      (generalMeanRows 935).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 935).c)).2-
      (generalMeanRows 935).J/2-(generalMeanRows 935).error 4 := by
  have he : (generalMeanRows 935).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 935) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 935)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0935

/-! Kernel-checked entropy margins for general spectral rectangle 936. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0936
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5281813656) (.branch 2 (.leaf 5112643796) (.leaf 4950676234))) (.branch 5 (.branch 4 (.leaf 4795511009) (.leaf 4646776198)) (.branch 6 (.leaf 4504125456) (.leaf 4367235831)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4235805803) (.leaf 4109553534)) (.branch 10 (.leaf 3988215284) (.leaf 3871543991))) (.branch 13 (.branch 12 (.leaf 3759307983) (.leaf 3651289815)) (.branch 14 (.leaf 3547285204) (.leaf 3447102074))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3350559672) (.branch 17 (.leaf 3257487769) (.leaf 3167725924))) (.branch 20 (.branch 19 (.leaf 3081122814) (.leaf 2997535611)) (.branch 21 (.leaf 2916829423) (.leaf 2838876760)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2763557063) (.leaf 2690756249)) (.branch 25 (.leaf 2620366308) (.leaf 2552284913))) (.branch 28 (.branch 27 (.leaf 2486415075) (.leaf 2422664813)) (.branch 29 (.leaf 2360946847) (.leaf 2301178320)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2243280529) (.branch 32 (.leaf 2187178689) (.leaf 2132801694))) (.branch 35 (.branch 34 (.leaf 2080081914) (.leaf 2028954990)) (.branch 36 (.leaf 1979359650) (.leaf 1931237534)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1884533035) (.leaf 1839193145)) (.branch 40 (.leaf 1795167310) (.leaf 1752407299))) (.branch 43 (.branch 42 (.leaf 1710867080) (.leaf 1670502698)) (.branch 44 (.leaf 1631272169) (.leaf 1593135374))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1556053959) (.branch 47 (.leaf 1519991249) (.leaf 1484912156))) (.branch 50 (.branch 49 (.leaf 1450783100) (.leaf 1417571934)) (.branch 51 (.leaf 1385247868) (.leaf 1353781404)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1323144270) (.leaf 1293309360)) (.branch 55 (.leaf 1264250677) (.leaf 1235943278))) (.branch 58 (.branch 57 (.leaf 1208363225) (.leaf 1181487535)) (.branch 59 (.leaf 1155294134) (.leaf 1129761814))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1104870195) (.branch 62 (.leaf 1080599682) (.leaf 1056931432))) (.branch 65 (.branch 64 (.leaf 1033847317) (.leaf 1011329893)) (.branch 66 (.leaf 989362366) (.leaf 967928568)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 947012921) (.leaf 926600419)) (.branch 70 (.leaf 906676596) (.leaf 887227507))) (.branch 73 (.branch 72 (.leaf 868239702) (.leaf 849700206)) (.branch 74 (.leaf 831596498) (.leaf 813916492))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 796648518) (.branch 77 (.leaf 779781306) (.leaf 763303967))) (.branch 80 (.branch 79 (.leaf 747205977) (.leaf 731477165)) (.branch 81 (.leaf 716107695) (.leaf 701088054)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 686409041) (.leaf 672061750)) (.branch 85 (.leaf 658037560) (.leaf 644328126))) (.branch 88 (.branch 87 (.leaf 630925365) (.leaf 617821449)) (.branch 89 (.leaf 605008790) (.leaf 592480038)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 580228065) (.branch 92 (.leaf 568245961) (.leaf 556527023))) (.branch 95 (.branch 94 (.leaf 545064750) (.leaf 533852833)) (.branch 96 (.leaf 522885150) (.leaf 512155758)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 501658886) (.leaf 491388931)) (.branch 100 (.leaf 481340449) (.leaf 471508151))) (.branch 103 (.branch 102 (.leaf 461886900) (.leaf 452471699)) (.branch 104 (.leaf 443257695) (.leaf 434240165))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 425414518) (.leaf 416776290)) (.branch 108 (.leaf 408321136) (.leaf 400044828))) (.branch 111 (.branch 110 (.leaf 391943253) (.leaf 384012407)) (.branch 112 (.leaf 376248392) (.leaf 368647412)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 361205771) (.leaf 353919869)) (.branch 116 (.leaf 346786199) (.leaf 339801344))) (.branch 119 (.branch 118 (.leaf 332961976) (.leaf 326264850)) (.branch 120 (.leaf 319706802) (.leaf 313284751)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 936).prefactor = (2313291841508743/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 936).cutoff/(generalMeanRows 936).c)).2 =
    (374979757348187/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 936).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 936).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 936).q*(generalMeanRows 936).cutoff/2-2 = (904/441:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable304.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 936).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 936

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 936).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 936).criticalRate j.val*(generalMeanRows 936).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 936).c*(generalMeanRows 936).criticalPoint j.val)).2-
      (generalMeanRows 936).J/2-(generalMeanRows 936).error (generalMeanGrid j.val)+
      (generalMeanRows 936).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 936).c)).2-
      (generalMeanRows 936).J/2-(generalMeanRows 936).error 4 := by
  have he : (generalMeanRows 936).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 936) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 936)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0936

/-! Kernel-checked entropy margins for general spectral rectangle 937. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0937
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5221244874) (.branch 2 (.leaf 5055925235) (.leaf 4897655792))) (.branch 5 (.branch 4 (.leaf 4746041546) (.leaf 4600715364)) (.branch 6 (.leaf 4461335538) (.leaf 4327583610)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4199162424) (.leaf 4075794375)) (.branch 10 (.leaf 3957219840) (.leaf 3843195759))) (.branch 13 (.branch 12 (.leaf 3733494353) (.leaf 3627901960)) (.branch 14 (.leaf 3526217984) (.leaf 3428253930))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3333832533) (.branch 17 (.leaf 3242786954) (.leaf 3154960051))) (.branch 20 (.branch 19 (.leaf 3070203706) (.leaf 2988378213)) (.branch 21 (.leaf 2909351707) (.leaf 2832999645)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2759204327) (.leaf 2687854447)) (.branch 25 (.leaf 2618844692) (.leaf 2552075353))) (.branch 28 (.branch 27 (.leaf 2487451980) (.leaf 2424885052)) (.branch 29 (.leaf 2364289677) (.leaf 2305585313)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2248695499) (.branch 32 (.leaf 2193547620) (.leaf 2140072675))) (.branch 35 (.branch 34 (.leaf 2088205068) (.leaf 2037882409)) (.branch 36 (.leaf 1989045332) (.leaf 1941637321)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1895604550) (.leaf 1850895732)) (.branch 40 (.leaf 1807461978) (.leaf 1765256664))) (.branch 43 (.branch 42 (.leaf 1724235310) (.leaf 1684355460)) (.branch 44 (.leaf 1645576576) (.leaf 1607859933))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1571168526) (.branch 47 (.leaf 1535466977) (.leaf 1500721450))) (.branch 50 (.branch 49 (.leaf 1466899572) (.leaf 1433970357)) (.branch 51 (.leaf 1401904138) (.leaf 1370672494)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1340248192) (.leaf 1310605127)) (.branch 55 (.leaf 1281718266) (.leaf 1253563591))) (.branch 58 (.branch 57 (.leaf 1226118056) (.leaf 1199359534)) (.branch 59 (.leaf 1173266777) (.leaf 1147819369))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1122997692) (.branch 62 (.leaf 1098782884) (.leaf 1075156804))) (.branch 65 (.branch 64 (.leaf 1052102000) (.leaf 1029601676)) (.branch 66 (.leaf 1007639663) (.leaf 986200389)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 965268852) (.leaf 944830594)) (.branch 70 (.leaf 924871679) (.leaf 905378667))) (.branch 73 (.branch 72 (.leaf 886338595) (.leaf 867738953)) (.branch 74 (.leaf 849567666) (.leaf 831813076))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 814463923) (.branch 77 (.leaf 797509328) (.leaf 780938777))) (.branch 80 (.branch 79 (.leaf 764742107) (.leaf 748909490)) (.branch 81 (.leaf 733431420) (.leaf 718298699)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 703502425) (.leaf 689033982)) (.branch 85 (.leaf 674885023) (.leaf 661047466))) (.branch 88 (.branch 87 (.leaf 647513480) (.leaf 634275475)) (.branch 89 (.leaf 621326094) (.leaf 608658203)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 596264884) (.branch 92 (.leaf 584139426) (.leaf 572275314))) (.branch 95 (.branch 94 (.leaf 560666230) (.leaf 549306035)) (.branch 96 (.leaf 538188772) (.leaf 527308653)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 516660057) (.leaf 506237521)) (.branch 100 (.leaf 496035736) (.leaf 486049540))) (.branch 103 (.branch 102 (.leaf 476273918) (.leaf 466703989)) (.branch 104 (.leaf 457335007) (.leaf 448162354))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 439181539) (.leaf 430388188)) (.branch 108 (.leaf 421778045) (.leaf 413346967))) (.branch 111 (.branch 110 (.leaf 405090919) (.leaf 397005971)) (.branch 112 (.leaf 389088296) (.leaf 381334165)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 373739944) (.leaf 366302092)) (.branch 116 (.leaf 359017158) (.leaf 351881777))) (.branch 119 (.branch 118 (.leaf 344892668) (.leaf 338046635)) (.branch 120 (.leaf 331340555) (.leaf 324771388)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 937).prefactor = (458327831372957/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 937).cutoff/(generalMeanRows 937).c)).2 =
    (392963789007893/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 937).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 937).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 937).q*(generalMeanRows 937).c/2-2 = (31/40:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable307.value]
    have hcontinuation : (generalMeanRows 937).q*(generalMeanRows 937).cutoff/2-2 = (724/343:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable308.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 937).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 937

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 937).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 937).criticalRate j.val*(generalMeanRows 937).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 937).c*(generalMeanRows 937).criticalPoint j.val)).2-
      (generalMeanRows 937).J/2-(generalMeanRows 937).error (generalMeanGrid j.val)+
      (generalMeanRows 937).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 937).c)).2-
      (generalMeanRows 937).J/2-(generalMeanRows 937).error 4 := by
  have he : (generalMeanRows 937).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 937) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 937)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0937

/-! Kernel-checked entropy margins for general spectral rectangle 938. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0938
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5202348180) (.branch 2 (.leaf 5033110940) (.leaf 4871147567))) (.branch 5 (.branch 4 (.leaf 4716051202) (.leaf 4567443623)) (.branch 6 (.leaf 4424972741) (.leaf 4288310366)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4157150201) (.leaf 4031206054)) (.branch 10 (.leaf 3910210217) (.leaf 3793912015))) (.branch 13 (.branch 12 (.leaf 3682076488) (.leaf 3574483195)) (.branch 14 (.leaf 3470925133) (.leaf 3371207750))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3275148046) (.branch 17 (.leaf 3182573751) (.leaf 3093322573))) (.branch 20 (.branch 19 (.leaf 3007241510) (.leaf 2924186217)) (.branch 21 (.leaf 2844020424) (.leaf 2766615401)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2691849464) (.leaf 2619607520)) (.branch 25 (.leaf 2549780642) (.leaf 2482265687))) (.branch 28 (.branch 27 (.leaf 2416964926) (.leaf 2353785714)) (.branch 29 (.leaf 2292640180) (.leaf 2233444932)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2176120798) (.branch 32 (.leaf 2120592564) (.leaf 2066788753))) (.branch 35 (.branch 34 (.leaf 2014641398) (.leaf 1964085843)) (.branch 36 (.leaf 1915060555) (.leaf 1867506945)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1821369202) (.leaf 1776594140)) (.branch 40 (.leaf 1733131050) (.leaf 1690931567))) (.branch 43 (.branch 42 (.leaf 1649949541) (.leaf 1610140918)) (.branch 44 (.leaf 1571463626) (.leaf 1533877472))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1497344041) (.branch 47 (.leaf 1461826605) (.leaf 1427290031))) (.branch 50 (.branch 49 (.leaf 1393700705) (.leaf 1361026449)) (.branch 51 (.leaf 1329236450) (.leaf 1298301191)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1268192385) (.leaf 1238882917)) (.branch 55 (.leaf 1210346781) (.leaf 1182559030))) (.branch 58 (.branch 57 (.leaf 1155495723) (.leaf 1129133873)) (.branch 59 (.leaf 1103451410) (.leaf 1078427125))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1054040640) (.branch 62 (.leaf 1030272364) (.leaf 1007103455))) (.branch 65 (.branch 64 (.leaf 984515790) (.leaf 962491925)) (.branch 66 (.leaf 941015073) (.leaf 920069064)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 899638327) (.leaf 879707855)) (.branch 70 (.leaf 860263185) (.leaf 841290371))) (.branch 73 (.branch 72 (.leaf 822775966) (.leaf 804706994)) (.branch 74 (.leaf 787070934) (.leaf 769855698))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 753049616) (.branch 77 (.leaf 736641415) (.leaf 720620202))) (.branch 80 (.branch 79 (.leaf 704975452) (.leaf 689696989)) (.branch 81 (.leaf 674774975) (.leaf 660199892)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 645962532) (.leaf 632053986)) (.branch 85 (.leaf 618465628) (.leaf 605189106))) (.branch 88 (.branch 87 (.leaf 592216333) (.leaf 579539473)) (.branch 89 (.leaf 567150934) (.leaf 555043357)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543209611) (.branch 92 (.leaf 531642777) (.leaf 520336147))) (.branch 95 (.branch 94 (.leaf 509283213) (.leaf 498477661)) (.branch 96 (.leaf 487913362) (.leaf 477584368)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 467484901) (.leaf 457609353)) (.branch 100 (.leaf 447952274) (.leaf 438508372))) (.branch 103 (.branch 102 (.leaf 429272503) (.leaf 420239667)) (.branch 104 (.leaf 411405005) (.leaf 402763792))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 394311434) (.leaf 386043461)) (.branch 108 (.leaf 377955527) (.leaf 370043403))) (.branch 111 (.branch 110 (.leaf 362302973) (.leaf 354730232)) (.branch 112 (.leaf 347321279) (.leaf 340072320)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 332979658) (.leaf 326039694)) (.branch 116 (.leaf 319248922) (.leaf 312603926))) (.branch 119 (.branch 118 (.leaf 306101379) (.leaf 299738038)) (.branch 120 (.leaf 293510745) (.leaf 287416419)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 938).prefactor = (1178182789898137/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 938).cutoff/(generalMeanRows 938).c)).2 =
    (379540768675747/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 938).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 938).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 938).q*(generalMeanRows 938).c/2-2 = (13/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable042.value]
    have hcontinuation : (generalMeanRows 938).q*(generalMeanRows 938).cutoff/2-2 = (724/343:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable308.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 938).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 938

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 938).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 938).criticalRate j.val*(generalMeanRows 938).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 938).c*(generalMeanRows 938).criticalPoint j.val)).2-
      (generalMeanRows 938).J/2-(generalMeanRows 938).error (generalMeanGrid j.val)+
      (generalMeanRows 938).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 938).c)).2-
      (generalMeanRows 938).J/2-(generalMeanRows 938).error 4 := by
  have he : (generalMeanRows 938).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 938) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 938)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0938

/-! Kernel-checked entropy margins for general spectral rectangle 939. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0939
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5266247272) (.branch 2 (.leaf 5092661174) (.leaf 4926566271))) (.branch 5 (.branch 4 (.leaf 4767543816) (.leaf 4615204510)) (.branch 6 (.leaf 4469185915) (.leaf 4329150166)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4194781913) (.leaf 4065786473)) (.branch 10 (.leaf 3941888176) (.leaf 3822828865))) (.branch 13 (.branch 12 (.leaf 3708366544) (.leaf 3598274150)) (.branch 14 (.leaf 3492338445) (.leaf 3390358993))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3292147245) (.branch 17 (.leaf 3197525688) (.leaf 3106327078))) (.branch 20 (.branch 19 (.leaf 3018393725) (.leaf 2933576851)) (.branch 21 (.leaf 2851735986) (.leaf 2772738418)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2696458689) (.leaf 2622778124)) (.branch 25 (.leaf 2551584399) (.leaf 2482771138))) (.branch 28 (.branch 27 (.leaf 2416237544) (.leaf 2351888056)) (.branch 29 (.leaf 2289632024) (.leaf 2229383417)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2171060544) (.branch 32 (.leaf 2114585799) (.leaf 2059885420))) (.branch 35 (.branch 34 (.leaf 2006889262) (.leaf 1955530596)) (.branch 36 (.leaf 1905745907) (.leaf 1857474716)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1810659408) (.leaf 1765245073)) (.branch 40 (.leaf 1721179357) (.leaf 1678412321))) (.branch 43 (.branch 42 (.leaf 1636896312) (.leaf 1596585838)) (.branch 44 (.leaf 1557437450) (.leaf 1519409641))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1482462737) (.branch 47 (.leaf 1446558802) (.leaf 1411661553))) (.branch 50 (.branch 49 (.leaf 1377736269) (.leaf 1344749712)) (.branch 51 (.leaf 1312670057) (.leaf 1281466814)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1251110766) (.leaf 1221573902)) (.branch 55 (.leaf 1192829361) (.leaf 1164851376))) (.branch 58 (.branch 57 (.leaf 1137615216) (.leaf 1111097142)) (.branch 59 (.leaf 1085274354) (.leaf 1060124952))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1035627887) (.branch 62 (.leaf 1011762928) (.leaf 988510618))) (.branch 65 (.branch 64 (.leaf 965852242) (.leaf 943769790)) (.branch 66 (.leaf 922245928) (.leaf 901263965)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 880807825) (.leaf 860862020)) (.branch 70 (.leaf 841411622) (.leaf 822442241))) (.branch 73 (.branch 72 (.leaf 803939999) (.leaf 785891509)) (.branch 74 (.leaf 768283856) (.leaf 751104571))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 734341618) (.branch 77 (.leaf 717983373) (.leaf 702018607))) (.branch 80 (.branch 79 (.leaf 686436469) (.leaf 671226473)) (.branch 81 (.leaf 656378479) (.leaf 641882683)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 627729600) (.leaf 613910054)) (.branch 85 (.leaf 600415163) (.leaf 587236331))) (.branch 88 (.branch 87 (.leaf 574365233) (.leaf 561793807)) (.branch 89 (.leaf 549514242) (.leaf 537518970)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 525800658) (.branch 92 (.leaf 514352194) (.leaf 503166684))) (.branch 95 (.branch 94 (.leaf 492237441) (.leaf 481557979)) (.branch 96 (.leaf 471122006) (.leaf 460923412)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 450956271) (.leaf 441214826)) (.branch 100 (.leaf 431693490) (.leaf 422386833))) (.branch 103 (.branch 102 (.leaf 413289584) (.leaf 404396619)) (.branch 104 (.leaf 395702959) (.leaf 387203767))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 378894338) (.leaf 370770098)) (.branch 108 (.leaf 362826601) (.leaf 355059520))) (.branch 111 (.branch 110 (.leaf 347464647) (.leaf 340037890)) (.branch 112 (.leaf 332775263) (.leaf 325672891)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 318726999) (.leaf 311933914)) (.branch 116 (.leaf 305290059) (.leaf 298791951))) (.branch 119 (.branch 118 (.leaf 292436197) (.leaf 286219494)) (.branch 120 (.leaf 280138622) (.leaf 274190446)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 939).prefactor = (4845840348831359/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 939).cutoff/(generalMeanRows 939).c)).2 =
    (372896225957081/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 939).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 939).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 939).q*(generalMeanRows 939).c/2-2 = (133/160:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable309.value]
    have hcontinuation : (generalMeanRows 939).q*(generalMeanRows 939).cutoff/2-2 = (724/343:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable308.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 939).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 939

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 939).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 939).criticalRate j.val*(generalMeanRows 939).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 939).c*(generalMeanRows 939).criticalPoint j.val)).2-
      (generalMeanRows 939).J/2-(generalMeanRows 939).error (generalMeanGrid j.val)+
      (generalMeanRows 939).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 939).c)).2-
      (generalMeanRows 939).J/2-(generalMeanRows 939).error 4 := by
  have he : (generalMeanRows 939).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 939) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 939)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0939

/-! Kernel-checked entropy margins for general spectral rectangle 940. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0940
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5331267827) (.branch 2 (.leaf 5153251066) (.leaf 4982948770))) (.branch 5 (.branch 4 (.leaf 4819929943) (.leaf 4663793857)) (.branch 6 (.leaf 4514167413) (.leaf 4370702770)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4233075241) (.leaf 4100981393)) (.branch 10 (.leaf 3974137343) (.leaf 3852277222))) (.branch 13 (.branch 12 (.leaf 3735151780) (.leaf 3622527130)) (.branch 14 (.leaf 3514183600) (.leaf 3409914693))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3309526138) (.branch 17 (.leaf 3212835018) (.leaf 3119668983))) (.branch 20 (.branch 19 (.leaf 3029865516) (.leaf 2943271265)) (.branch 21 (.leaf 2859741432) (.leaf 2779139206)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2701335239) (.leaf 2626207167)) (.branch 25 (.leaf 2553639162) (.leaf 2483521525))) (.branch 28 (.branch 27 (.leaf 2415750297) (.leaf 2350226913)) (.branch 29 (.leaf 2286857865) (.leaf 2225554403)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2166232249) (.branch 32 (.leaf 2108811330) (.leaf 2053215536))) (.branch 35 (.branch 34 (.leaf 1999372484) (.leaf 1947213311)) (.branch 36 (.leaf 1896672466) (.leaf 1847687527)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1800199027) (.leaf 1754150285)) (.branch 40 (.leaf 1709487257) (.leaf 1666158390))) (.branch 43 (.branch 42 (.leaf 1624114485) (.leaf 1583308577)) (.branch 44 (.leaf 1543695807) (.leaf 1505233318))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1467880146) (.branch 47 (.leaf 1431597121) (.leaf 1396346777))) (.branch 50 (.branch 49 (.leaf 1362093262) (.leaf 1328802256)) (.branch 51 (.leaf 1296440896) (.leaf 1264977697)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1234382491) (.leaf 1204626355)) (.branch 55 (.leaf 1175681555) (.leaf 1147521483))) (.branch 58 (.branch 57 (.leaf 1120120607) (.leaf 1093454415)) (.branch 59 (.leaf 1067499371) (.leaf 1042232864))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1017633167) (.branch 62 (.leaf 993679395) (.leaf 970351466))) (.branch 65 (.branch 64 (.leaf 947630064) (.leaf 925496604)) (.branch 66 (.leaf 903933199) (.leaf 882922625)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 862448298) (.leaf 842494240)) (.branch 70 (.leaf 823045053) (.leaf 804085896))) (.branch 73 (.branch 72 (.leaf 785602458) (.leaf 767580937)) (.branch 74 (.leaf 750008016) (.leaf 732870845))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 716157019) (.branch 77 (.leaf 699854560) (.leaf 683951898))) (.branch 80 (.branch 79 (.leaf 668437858) (.leaf 653301639)) (.branch 81 (.leaf 638532801) (.leaf 624121249)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 610057222) (.leaf 596331277)) (.branch 85 (.leaf 582934276) (.leaf 569857377))) (.branch 88 (.branch 87 (.leaf 557092019) (.leaf 544629913)) (.branch 89 (.leaf 532463031) (.leaf 520583596)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 508984073) (.branch 92 (.leaf 497657159) (.leaf 486595774))) (.branch 95 (.branch 94 (.leaf 475793055) (.leaf 465242345)) (.branch 96 (.leaf 454937188) (.leaf 444871319)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 435038660) (.leaf 425433311)) (.branch 100 (.leaf 416049546) (.leaf 406881804))) (.branch 103 (.branch 102 (.leaf 397924685) (.leaf 389172944)) (.branch 104 (.leaf 380621487) (.leaf 372265363))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 364099761) (.leaf 356120005)) (.branch 108 (.leaf 348321550) (.leaf 340699976))) (.branch 111 (.branch 110 (.leaf 333250986) (.leaf 325970399)) (.branch 112 (.leaf 318854151) (.leaf 311898285)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 305098953) (.leaf 298452410)) (.branch 116 (.leaf 291955010) (.leaf 285603206))) (.branch 119 (.branch 118 (.leaf 279393542) (.leaf 273322656)) (.branch 120 (.leaf 267387272) (.leaf 261584200)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 940).prefactor = (2491354576694363/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 940).cutoff/(generalMeanRows 940).c)).2 =
    (36629554192573/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 940).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 940).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 940).q*(generalMeanRows 940).c/2-2 = (17/20:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable055.value]
    have hcontinuation : (generalMeanRows 940).q*(generalMeanRows 940).cutoff/2-2 = (724/343:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable308.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 940).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 940

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 940).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 940).criticalRate j.val*(generalMeanRows 940).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 940).c*(generalMeanRows 940).criticalPoint j.val)).2-
      (generalMeanRows 940).J/2-(generalMeanRows 940).error (generalMeanGrid j.val)+
      (generalMeanRows 940).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 940).c)).2-
      (generalMeanRows 940).J/2-(generalMeanRows 940).error 4 := by
  have he : (generalMeanRows 940).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 940) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 940)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0940

/-! Kernel-checked entropy margins for general spectral rectangle 941. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0941
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5665815556) (.branch 2 (.leaf 5483954904) (.leaf 5309879764))) (.branch 5 (.branch 4 (.leaf 5143154324) (.leaf 4983373483)) (.branch 6 (.leaf 4830160164) (.leaf 4683162911)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4542053748) (.leaf 4406526253)) (.branch 10 (.leaf 4276293822) (.leaf 4151088110))) (.branch 13 (.branch 12 (.leaf 4030657618) (.leaf 3914766413)) (.branch 14 (.leaf 3803192966) (.leaf 3695729090))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3592178982) (.branch 17 (.leaf 3492358337) (.leaf 3396093542))) (.branch 20 (.branch 19 (.leaf 3303220940) (.leaf 3213586148)) (.branch 21 (.leaf 3127043434) (.leaf 3043455146)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2962691176) (.leaf 2884628478)) (.branch 25 (.leaf 2809150610) (.leaf 2736147322))) (.branch 28 (.branch 27 (.leaf 2665514163) (.leaf 2597152126)) (.branch 29 (.leaf 2530967313) (.leaf 2466870624)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2404777470) (.branch 32 (.leaf 2344607506) (.leaf 2286284378))) (.branch 35 (.branch 34 (.leaf 2229735495) (.leaf 2174891805)) (.branch 36 (.leaf 2121687597) (.leaf 2070060309)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2019950350) (.leaf 1971300938)) (.branch 40 (.leaf 1924057937) (.leaf 1878169720))) (.branch 43 (.branch 42 (.leaf 1833587025) (.leaf 1790262831)) (.branch 44 (.leaf 1748152237) (.leaf 1707212348))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1667402170) (.branch 47 (.leaf 1628682509) (.leaf 1591015878))) (.branch 50 (.branch 49 (.leaf 1554366409) (.leaf 1518699770)) (.branch 51 (.leaf 1483983084) (.leaf 1450184861)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1417274922) (.leaf 1385224336)) (.branch 55 (.leaf 1354005360) (.leaf 1323591379))) (.branch 58 (.branch 57 (.leaf 1293956851) (.leaf 1265077253)) (.branch 59 (.leaf 1236929036) (.leaf 1209489576))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1182737128) (.branch 62 (.leaf 1156650790) (.leaf 1131210459))) (.branch 65 (.branch 64 (.leaf 1106396793) (.leaf 1082191182)) (.branch 66 (.leaf 1058575707) (.leaf 1035533115)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1013046782) (.leaf 991100693)) (.branch 70 (.leaf 969679408) (.leaf 948768039))) (.branch 73 (.branch 72 (.leaf 928352226) (.leaf 908418115)) (.branch 74 (.leaf 888952334) (.leaf 869941973))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 851374565) (.branch 77 (.leaf 833238066) (.leaf 815520838))) (.branch 80 (.branch 79 (.leaf 798211634) (.leaf 781299576)) (.branch 81 (.leaf 764774146) (.leaf 748625170)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 732842802) (.leaf 717417509)) (.branch 85 (.leaf 702340067) (.leaf 687601538))) (.branch 88 (.branch 87 (.leaf 673193266) (.leaf 659106866)) (.branch 89 (.leaf 645334206) (.leaf 631867409)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 618698833) (.branch 92 (.leaf 605821066) (.leaf 593226921))) (.branch 95 (.branch 94 (.leaf 580909420) (.leaf 568861794)) (.branch 96 (.leaf 557077469) (.leaf 545550063)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 534273378) (.leaf 523241393)) (.branch 100 (.leaf 512448258) (.leaf 501888288))) (.branch 103 (.branch 102 (.leaf 491555957) (.leaf 481445892)) (.branch 104 (.leaf 471552870) (.leaf 461871809))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 452397769) (.leaf 443125941)) (.branch 108 (.leaf 434051646) (.leaf 425170331))) (.branch 111 (.branch 110 (.leaf 416477562) (.leaf 407969024)) (.branch 112 (.leaf 399640515) (.leaf 391487942)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 383507319) (.leaf 375694762)) (.branch 116 (.leaf 368046487) (.leaf 360558807))) (.branch 119 (.branch 118 (.leaf 353228128) (.leaf 346050947)) (.branch 120 (.leaf 339023848) (.leaf 332143501)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 941).prefactor = (1263146619809949/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 941).cutoff/(generalMeanRows 941).c)).2 =
    (386229756826547/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 941).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 941).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 941).q*(generalMeanRows 941).cutoff/2-2 = (724/343:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable308.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 941).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 941

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 941).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 941).criticalRate j.val*(generalMeanRows 941).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 941).c*(generalMeanRows 941).criticalPoint j.val)).2-
      (generalMeanRows 941).J/2-(generalMeanRows 941).error (generalMeanGrid j.val)+
      (generalMeanRows 941).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 941).c)).2-
      (generalMeanRows 941).J/2-(generalMeanRows 941).error 4 := by
  have he : (generalMeanRows 941).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 941) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 941)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0941

/-! Kernel-checked entropy margins for general spectral rectangle 942. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0942
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7449035802) (.branch 2 (.leaf 7240386582) (.leaf 7039774592))) (.branch 5 (.branch 4 (.leaf 6846784526) (.leaf 6661029581)) (.branch 6 (.leaf 6482148887) (.leaf 6309805229)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6143683021) (.leaf 5983486501)) (.branch 10 (.leaf 5828938120) (.leaf 5679777088))) (.branch 13 (.branch 12 (.leaf 5535758077) (.leaf 5396650040)) (.branch 14 (.leaf 5262235154) (.leaf 5132307853))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5006673955) (.branch 17 (.leaf 4885149866) (.leaf 4767561853))) (.branch 20 (.branch 19 (.leaf 4653745378) (.leaf 4543544492)) (.branch 21 (.leaf 4436811277) (.leaf 4333405331)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4233193295) (.leaf 4136048422)) (.branch 25 (.leaf 4041850170) (.leaf 3950483830))) (.branch 28 (.branch 27 (.leaf 3861840185) (.leaf 3775815186)) (.branch 29 (.leaf 3692309657) (.leaf 3611229020)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3532483035) (.branch 32 (.leaf 3455985563) (.leaf 3381654340))) (.branch 35 (.branch 34 (.leaf 3309410770) (.leaf 3239179730)) (.branch 36 (.leaf 3170889384) (.leaf 3104471017)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3039858867) (.leaf 2976989982)) (.branch 40 (.leaf 2915804072) (.leaf 2856243382))) (.branch 43 (.branch 42 (.leaf 2798252561) (.leaf 2741778547)) (.branch 44 (.leaf 2686770454) (.leaf 2633179470))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2580958757) (.branch 47 (.leaf 2530063356) (.leaf 2480450100))) (.branch 50 (.branch 49 (.leaf 2432077532) (.leaf 2384905822)) (.branch 51 (.leaf 2338896697) (.leaf 2294013369)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2250220466) (.leaf 2207483970)) (.branch 55 (.leaf 2165771157) (.leaf 2125050539))) (.branch 58 (.branch 57 (.leaf 2085291811) (.leaf 2046465797)) (.branch 59 (.leaf 2008544406) (.leaf 1971500579))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1935308249) (.branch 62 (.leaf 1899942299) (.leaf 1865378520))) (.branch 65 (.branch 64 (.leaf 1831593572) (.leaf 1798564952)) (.branch 66 (.leaf 1766270956) (.leaf 1734690646)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1703803819) (.leaf 1673590978)) (.branch 70 (.leaf 1644033304) (.leaf 1615112625))) (.branch 73 (.branch 72 (.leaf 1586811393) (.leaf 1559112661)) (.branch 74 (.leaf 1532000052) (.leaf 1505457745))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1479470447) (.branch 77 (.leaf 1454023376) (.leaf 1429102240))) (.branch 80 (.branch 79 (.leaf 1404693216) (.leaf 1380782935)) (.branch 81 (.leaf 1357358462) (.leaf 1334407283)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1311917285) (.leaf 1289876743)) (.branch 85 (.leaf 1268274304) (.leaf 1247098977))) (.branch 88 (.branch 87 (.leaf 1226340113) (.leaf 1205987399)) (.branch 89 (.leaf 1186030840) (.leaf 1166460752)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1147267747) (.branch 92 (.leaf 1128442724) (.leaf 1109976859))) (.branch 95 (.branch 94 (.leaf 1091861593) (.leaf 1074088626)) (.branch 96 (.leaf 1056649904) (.leaf 1039537611)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1022744163) (.leaf 1006262199)) (.branch 100 (.leaf 990084570) (.leaf 974204335))) (.branch 103 (.branch 102 (.leaf 958614753) (.leaf 943309277)) (.branch 104 (.leaf 928281544) (.leaf 913525373))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 899034754) (.leaf 884803848)) (.branch 108 (.leaf 870826976) (.leaf 857098618))) (.branch 111 (.branch 110 (.leaf 843613401) (.leaf 830366104)) (.branch 112 (.leaf 817351644) (.leaf 804565075)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 792001585) (.leaf 779656490)) (.branch 116 (.leaf 767525228) (.leaf 755603359))) (.branch 119 (.branch 118 (.leaf 743886558) (.leaf 732370613)) (.branch 120 (.leaf 721051420) (.leaf 709924980)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 942).prefactor = (4869665035030099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 942).cutoff/(generalMeanRows 942).c)).2 =
    (7834091227081/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 942).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 942).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 942).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 942

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 942).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 942).criticalRate j.val*(generalMeanRows 942).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 942).c*(generalMeanRows 942).criticalPoint j.val)).2-
      (generalMeanRows 942).J/2-(generalMeanRows 942).error (generalMeanGrid j.val)+
      (generalMeanRows 942).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 942).c)).2-
      (generalMeanRows 942).J/2-(generalMeanRows 942).error 4 := by
  have he : (generalMeanRows 942).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 942) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 942)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0942

/-! Kernel-checked entropy margins for general spectral rectangle 943. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0943
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7153036043) (.branch 2 (.leaf 6944941312) (.leaf 6744961654))) (.branch 5 (.branch 4 (.leaf 6552676840) (.leaf 6367695431)) (.branch 6 (.leaf 6189652192) (.leaf 6018205799)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5853036797) (.leaf 5693845789)) (.branch 10 (.leaf 5540351800) (.leaf 5392290820))) (.branch 13 (.branch 12 (.leaf 5249414488) (.leaf 5111488907)) (.branch 14 (.leaf 4978293570) (.leaf 4849620386))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4725272799) (.branch 17 (.leaf 4605064978) (.leaf 4488821085))) (.branch 20 (.branch 19 (.leaf 4376374604) (.leaf 4267567721)) (.branch 21 (.leaf 4162250762) (.leaf 4060281673)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3961525541) (.leaf 3865854152)) (.branch 25 (.leaf 3773145584) (.leaf 3683283831))) (.branch 28 (.branch 27 (.leaf 3596158448) (.leaf 3511664233)) (.branch 29 (.leaf 3429700924) (.leaf 3350172917)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3272989005) (.branch 32 (.leaf 3198062139) (.leaf 3125309195))) (.branch 35 (.branch 34 (.leaf 3054650768) (.leaf 2986010969)) (.branch 36 (.leaf 2919317241) (.leaf 2854500186)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2791493402) (.leaf 2730233328)) (.branch 40 (.leaf 2670659102) (.leaf 2612712425))) (.branch 43 (.branch 42 (.leaf 2556337435) (.leaf 2501480586)) (.branch 44 (.leaf 2448090535) (.leaf 2396118037))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2345515843) (.branch 47 (.leaf 2296238607) (.leaf 2248242796))) (.branch 50 (.branch 49 (.leaf 2201486603) (.leaf 2155929870)) (.branch 51 (.leaf 2111534013) (.leaf 2068261946)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2026078017) (.leaf 1984947942)) (.branch 55 (.leaf 1944838744) (.leaf 1905718694))) (.branch 58 (.branch 57 (.leaf 1867557260) (.leaf 1830325049)) (.branch 59 (.leaf 1793993763) (.leaf 1758536149))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1723925951) (.branch 62 (.leaf 1690137876) (.leaf 1657147544))) (.branch 65 (.branch 64 (.leaf 1624931457) (.leaf 1593466956)) (.branch 66 (.leaf 1562732191) (.leaf 1532706085)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1503368301) (.leaf 1474699215)) (.branch 70 (.leaf 1446679886) (.leaf 1419292027))) (.branch 73 (.branch 72 (.leaf 1392517978) (.leaf 1366340686)) (.branch 74 (.leaf 1340743674) (.leaf 1315711022))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1291227346) (.branch 77 (.leaf 1267277775) (.leaf 1243847930))) (.branch 80 (.branch 79 (.leaf 1220923909) (.leaf 1198492263)) (.branch 81 (.leaf 1176539985) (.leaf 1155054488)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1134023591) (.leaf 1113435503)) (.branch 85 (.leaf 1093278809) (.leaf 1073542458))) (.branch 88 (.branch 87 (.leaf 1054215743) (.leaf 1035288296)) (.branch 89 (.leaf 1016750070) (.leaf 998591330)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 980802640) (.branch 92 (.leaf 963374853) (.leaf 946299102))) (.branch 95 (.branch 94 (.leaf 929566786) (.leaf 913169564)) (.branch 96 (.leaf 897099343) (.leaf 881348273)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 865908735) (.leaf 850773334)) (.branch 100 (.leaf 835934890) (.leaf 821386433))) (.branch 103 (.branch 102 (.leaf 807121195) (.leaf 793132600)) (.branch 104 (.leaf 779414263) (.leaf 765959976))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 752763711) (.leaf 739819607)) (.branch 108 (.leaf 727121964) (.leaf 714665245))) (.branch 111 (.branch 110 (.leaf 702444062) (.leaf 690453177)) (.branch 112 (.leaf 678687494) (.leaf 667142054)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 655812033) (.leaf 644692737)) (.branch 116 (.leaf 633779594) (.leaf 623068158))) (.branch 119 (.branch 118 (.leaf 612554095) (.leaf 602233188)) (.branch 120 (.leaf 592101328) (.leaf 582154514)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 943).prefactor = (307519965359859/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 943).cutoff/(generalMeanRows 943).c)).2 =
    (302417771105549/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 943).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 943).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 943).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 943

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 943).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 943).criticalRate j.val*(generalMeanRows 943).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 943).c*(generalMeanRows 943).criticalPoint j.val)).2-
      (generalMeanRows 943).J/2-(generalMeanRows 943).error (generalMeanGrid j.val)+
      (generalMeanRows 943).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 943).c)).2-
      (generalMeanRows 943).J/2-(generalMeanRows 943).error 4 := by
  have he : (generalMeanRows 943).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 943) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 943)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0943

/-! Kernel-checked entropy margins for general spectral rectangle 944. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0944
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6885395007) (.branch 2 (.leaf 6688158555) (.leaf 6498686607))) (.branch 5 (.branch 4 (.leaf 6316571783) (.leaf 6141434687)) (.branch 6 (.leaf 5972921408) (.leaf 5810701302)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5654465024) (.leaf 5503922759)) (.branch 10 (.leaf 5358802650) (.leaf 5218849375))) (.branch 13 (.branch 12 (.leaf 5083822874) (.leaf 4953497190)) (.branch 14 (.leaf 4827659431) (.leaf 4706108817))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4588655820) (.branch 17 (.leaf 4475121380) (.leaf 4365336184))) (.branch 20 (.branch 19 (.leaf 4259140014) (.leaf 4156381140)) (.branch 21 (.leaf 4056915773) (.leaf 3960607551)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3867327074) (.leaf 3776951472)) (.branch 25 (.leaf 3689364002) (.leaf 3604453682))) (.branch 28 (.branch 27 (.leaf 3522114947) (.leaf 3442247330)) (.branch 29 (.leaf 3364755168) (.leaf 3289547327)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3216536944) (.branch 32 (.leaf 3145641192) (.leaf 3076781054))) (.branch 35 (.branch 34 (.leaf 3009881116) (.leaf 2944869376)) (.branch 36 (.leaf 2881677053) (.leaf 2820238428)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2760490674) (.leaf 2702373711)) (.branch 40 (.leaf 2645830066) (.leaf 2590804735))) (.branch 43 (.branch 42 (.leaf 2537245066) (.leaf 2485100633)) (.branch 44 (.leaf 2434323135) (.leaf 2384866282))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2336685706) (.branch 47 (.leaf 2289738861) (.leaf 2243984941))) (.branch 50 (.branch 49 (.leaf 2199384793) (.leaf 2155900842)) (.branch 51 (.leaf 2113497014) (.leaf 2072138669)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2031792535) (.leaf 1992426640)) (.branch 55 (.leaf 1954010261) (.leaf 1916513860))) (.branch 58 (.branch 57 (.leaf 1879909033) (.leaf 1844168463)) (.branch 59 (.leaf 1809265866) (.leaf 1775175949))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1741874365) (.branch 62 (.leaf 1709337672) (.leaf 1677543296))) (.branch 65 (.branch 64 (.leaf 1646469489) (.leaf 1616095297)) (.branch 66 (.leaf 1586400526) (.leaf 1557365709)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1528972074) (.leaf 1501201519)) (.branch 70 (.leaf 1474036580) (.leaf 1447460405))) (.branch 73 (.branch 72 (.leaf 1421456731) (.leaf 1396009859)) (.branch 74 (.leaf 1371104629) (.leaf 1346726402))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1322861034) (.branch 77 (.leaf 1299494862) (.leaf 1276614679))) (.branch 80 (.branch 79 (.leaf 1254207720) (.leaf 1232261642)) (.branch 81 (.leaf 1210764510) (.leaf 1189704776)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1169071273) (.leaf 1148853189)) (.branch 85 (.leaf 1129040063) (.leaf 1109621765))) (.branch 88 (.branch 87 (.leaf 1090588488) (.leaf 1071930732)) (.branch 89 (.leaf 1053639295) (.leaf 1035705259)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1018119984) (.branch 92 (.leaf 1000875094) (.leaf 983962466))) (.branch 95 (.branch 94 (.leaf 967374226) (.leaf 951102734)) (.branch 96 (.leaf 935140581) (.leaf 919480575)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 904115737) (.leaf 889039294)) (.branch 100 (.leaf 874244666) (.leaf 859725468))) (.branch 103 (.branch 102 (.leaf 845475495) (.leaf 831488720)) (.branch 104 (.leaf 817759286) (.leaf 804281501))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 791049834) (.leaf 778058904)) (.branch 108 (.leaf 765303482) (.leaf 752778480))) (.branch 111 (.branch 110 (.leaf 740478949) (.leaf 728400075)) (.branch 112 (.leaf 716537170) (.leaf 704885676)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 693441151) (.leaf 682199273)) (.branch 116 (.leaf 671155833) (.leaf 660306729))) (.branch 119 (.branch 118 (.leaf 649647968) (.leaf 639175657)) (.branch 120 (.leaf 628886002) (.leaf 618775309)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 944).prefactor = (953346161314799/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 944).cutoff/(generalMeanRows 944).c)).2 =
    (331815542678501/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 944).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 944).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 944).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 944

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 944).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 944).criticalRate j.val*(generalMeanRows 944).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 944).c*(generalMeanRows 944).criticalPoint j.val)).2-
      (generalMeanRows 944).J/2-(generalMeanRows 944).error (generalMeanGrid j.val)+
      (generalMeanRows 944).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 944).c)).2-
      (generalMeanRows 944).J/2-(generalMeanRows 944).error 4 := by
  have he : (generalMeanRows 944).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 944) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 944)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0944

/-! Kernel-checked entropy margins for general spectral rectangle 945. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0945
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6635460750) (.branch 2 (.leaf 6440112066) (.leaf 6252538483))) (.branch 5 (.branch 4 (.leaf 6072330447) (.leaf 5899106532)) (.branch 6 (.leaf 5732510938) (.leaf 5572211267)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5417896547) (.leaf 5269275464)) (.branch 10 (.leaf 5126074775) (.leaf 4988037887))) (.branch 13 (.branch 12 (.leaf 4854923570) (.leaf 4726504802)) (.branch 14 (.leaf 4602567713) (.leaf 4482910637))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4367343241) (.branch 17 (.leaf 4255685735) (.leaf 4147768152))) (.branch 20 (.branch 19 (.leaf 4043429682) (.leaf 3942518070)) (.branch 21 (.leaf 3844889054) (.leaf 3750405858)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3658938716) (.leaf 3570364438)) (.branch 25 (.leaf 3484566006) (.leaf 3401432198))) (.branch 28 (.branch 27 (.leaf 3320857250) (.leaf 3242740526)) (.branch 29 (.leaf 3166986228) (.leaf 3093503112)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3022204233) (.branch 32 (.leaf 2953006706) (.leaf 2885831476))) (.branch 35 (.branch 34 (.leaf 2820603113) (.leaf 2757249613)) (.branch 36 (.leaf 2695702215) (.leaf 2635895228)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2577765872) (.leaf 2521254123)) (.branch 40 (.leaf 2466302573) (.leaf 2412856298))) (.branch 43 (.branch 42 (.leaf 2360862727) (.leaf 2310271530)) (.branch 44 (.leaf 2261034502) (.leaf 2213105458))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2166440140) (.branch 47 (.leaf 2120996114) (.leaf 2076732690))) (.branch 50 (.branch 49 (.leaf 2033610836) (.leaf 1991593096)) (.branch 51 (.leaf 1950643523) (.leaf 1910727600)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1871812179) (.leaf 1833865416)) (.branch 55 (.leaf 1796856713) (.leaf 1760756658))) (.branch 58 (.branch 57 (.leaf 1725536974) (.leaf 1691170466)) (.branch 59 (.leaf 1657630975) (.leaf 1624893331))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1592933307) (.branch 62 (.leaf 1561727581) (.leaf 1531253697))) (.branch 65 (.branch 64 (.leaf 1501490023) (.leaf 1472415720)) (.branch 66 (.leaf 1444010706) (.leaf 1416255624)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1389131810) (.leaf 1362621268)) (.branch 70 (.leaf 1336706637) (.leaf 1311371168))) (.branch 73 (.branch 72 (.leaf 1286598697) (.leaf 1262373621)) (.branch 74 (.leaf 1238680876) (.leaf 1215505914))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1192834683) (.branch 77 (.leaf 1170653607) (.leaf 1148949564))) (.branch 80 (.branch 79 (.leaf 1127709875) (.leaf 1106922276)) (.branch 81 (.leaf 1086574913) (.leaf 1066656315)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1047155390) (.leaf 1028061400)) (.branch 85 (.leaf 1009363954) (.leaf 991052993))) (.branch 88 (.branch 87 (.leaf 973118777) (.leaf 955551871)) (.branch 89 (.leaf 938343138) (.leaf 921483723)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 904965045) (.branch 92 (.leaf 888778788) (.leaf 872916887))) (.branch 95 (.branch 94 (.leaf 857371524) (.leaf 842135114)) (.branch 96 (.leaf 827200300) (.leaf 812559943)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 798207116) (.leaf 784135092)) (.branch 100 (.leaf 770337343) (.leaf 756807529))) (.branch 103 (.branch 102 (.leaf 743539491) (.leaf 730527248)) (.branch 104 (.leaf 717764988) (.leaf 705247061))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 692967977) (.leaf 680922400)) (.branch 108 (.leaf 669105138) (.leaf 657511144))) (.branch 111 (.branch 110 (.leaf 646135510) (.leaf 634973457)) (.branch 112 (.leaf 624020339) (.leaf 613271631)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 602722932) (.leaf 592369952)) (.branch 116 (.leaf 582208520) (.leaf 572234568))) (.branch 119 (.branch 118 (.leaf 562444138) (.leaf 552833372)) (.branch 120 (.leaf 543398510) (.leaf 534135889)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 945).prefactor = (4786788684913803/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 945).cutoff/(generalMeanRows 945).c)).2 =
    (16391969714943/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 945).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 945).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 945).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 945

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 945).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 945).criticalRate j.val*(generalMeanRows 945).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 945).c*(generalMeanRows 945).criticalPoint j.val)).2-
      (generalMeanRows 945).J/2-(generalMeanRows 945).error (generalMeanGrid j.val)+
      (generalMeanRows 945).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 945).c)).2-
      (generalMeanRows 945).J/2-(generalMeanRows 945).error 4 := by
  have he : (generalMeanRows 945).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 945) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 945)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0945

/-! Kernel-checked entropy margins for general spectral rectangle 946. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0946
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6238810527) (.branch 2 (.leaf 6046463424) (.leaf 5861897611))) (.branch 5 (.branch 4 (.leaf 5684701903) (.leaf 5514493320)) (.branch 6 (.leaf 5350914586) (.leaf 5193631909)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5042333005) (.leaf 4896725325)) (.branch 10 (.leaf 4756534469) (.leaf 4621502762))) (.branch 13 (.branch 12 (.leaf 4491387967) (.leaf 4365962119)) (.branch 14 (.leaf 4245010477) (.leaf 4128330563))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4015731294) (.branch 17 (.leaf 3907032186) (.leaf 3802062629))) (.branch 20 (.branch 19 (.leaf 3700661222) (.leaf 3602675165)) (.branch 21 (.leaf 3507959698) (.leaf 3416377587)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3327798644) (.leaf 3242099296)) (.branch 25 (.leaf 3159162173) (.leaf 3078875737))) (.branch 28 (.branch 27 (.leaf 3001133932) (.leaf 2925835861)) (.branch 29 (.leaf 2852885486) (.leaf 2782191350)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2713666316) (.branch 32 (.leaf 2647227324) (.leaf 2582795166))) (.branch 35 (.branch 34 (.leaf 2520294275) (.leaf 2459652525)) (.branch 36 (.leaf 2400801046) (.leaf 2343674056)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2288208691) (.leaf 2234344858)) (.branch 40 (.leaf 2182025088) (.leaf 2131194406))) (.branch 43 (.branch 42 (.leaf 2081800201) (.leaf 2033792107)) (.branch 44 (.leaf 1987121891) (.leaf 1941743352))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1897612213) (.branch 47 (.leaf 1854686035) (.leaf 1812924123))) (.branch 50 (.branch 49 (.leaf 1772287444) (.leaf 1732738551)) (.branch 51 (.leaf 1694241503) (.leaf 1656761795)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1620266295) (.leaf 1584723178)) (.branch 55 (.leaf 1550101864) (.leaf 1516372966))) (.branch 58 (.branch 57 (.leaf 1483508231) (.leaf 1451480491)) (.branch 59 (.leaf 1420263616) (.leaf 1389832465))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1360162843) (.branch 62 (.leaf 1331231461) (.leaf 1303015896))) (.branch 65 (.branch 64 (.leaf 1275494552) (.leaf 1248646624)) (.branch 66 (.leaf 1222452068) (.leaf 1196891564)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1171946487) (.leaf 1147598878)) (.branch 70 (.leaf 1123831417) (.leaf 1100627395))) (.branch 73 (.branch 72 (.leaf 1077970688) (.leaf 1055845734)) (.branch 74 (.leaf 1034237512) (.leaf 1013131516))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 992513735) (.branch 77 (.leaf 972370638) (.leaf 952689146))) (.branch 80 (.branch 79 (.leaf 933456623) (.leaf 914660851)) (.branch 81 (.leaf 896290020) (.leaf 878332705)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 860777860) (.leaf 843614792)) (.branch 85 (.leaf 826833159) (.leaf 810422948))) (.branch 88 (.branch 87 (.leaf 794374466) (.leaf 778678328)) (.branch 89 (.leaf 763325444) (.leaf 748307009)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 733614493) (.branch 92 (.leaf 719239628) (.leaf 705174402))) (.branch 95 (.branch 94 (.leaf 691411047) (.leaf 677942030)) (.branch 96 (.leaf 664760046) (.leaf 651858010)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 639229048) (.leaf 626866487)) (.branch 100 (.leaf 614763855) (.leaf 602914865))) (.branch 103 (.branch 102 (.leaf 591313417) (.leaf 579953583)) (.branch 104 (.leaf 568829609) (.leaf 557935904))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 547267035) (.leaf 536817725)) (.branch 108 (.leaf 526582842) (.leaf 516557399))) (.branch 111 (.branch 110 (.leaf 506736546) (.leaf 497115569)) (.branch 112 (.leaf 487689880) (.leaf 478455020)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 469406647) (.leaf 460540538)) (.branch 116 (.leaf 451852584) (.leaf 443338782))) (.branch 119 (.branch 118 (.leaf 434995239) (.leaf 426818163)) (.branch 120 (.leaf 418803859) (.leaf 410948733)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 946).prefactor = (4795360769954721/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 946).cutoff/(generalMeanRows 946).c)).2 =
    (156954775144341/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 946).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 946).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 946).q*(generalMeanRows 946).c/2-2 = (1427/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable259.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 946).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 946

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 946).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 946).criticalRate j.val*(generalMeanRows 946).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 946).c*(generalMeanRows 946).criticalPoint j.val)).2-
      (generalMeanRows 946).J/2-(generalMeanRows 946).error (generalMeanGrid j.val)+
      (generalMeanRows 946).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 946).c)).2-
      (generalMeanRows 946).J/2-(generalMeanRows 946).error 4 := by
  have he : (generalMeanRows 946).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 946) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 946)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0946

/-! Kernel-checked entropy margins for general spectral rectangle 947. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0947
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5816455007) (.branch 2 (.leaf 5628128498) (.leaf 5447570747))) (.branch 5 (.branch 4 (.leaf 5274369457) (.leaf 5108140572)) (.branch 6 (.leaf 4948525787) (.leaf 4795190331)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4647820990) (.leaf 4506124342)) (.branch 10 (.leaf 4369825167) (.leaf 4238665025))) (.branch 13 (.branch 12 (.leaf 4112400966) (.leaf 3990804365)) (.branch 14 (.leaf 3873659871) (.leaf 3760764446))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3651926492) (.branch 17 (.leaf 3546965055) (.leaf 3445709100))) (.branch 20 (.branch 19 (.leaf 3347996837) (.leaf 3253675120)) (.branch 21 (.leaf 3162598874) (.leaf 3074630585)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2989639821) (.leaf 2907502789)) (.branch 25 (.leaf 2828101930) (.leaf 2751325543))) (.branch 28 (.branch 27 (.leaf 2677067433) (.leaf 2605226585)) (.branch 29 (.leaf 2535706866) (.leaf 2468416745)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2403269024) (.branch 32 (.leaf 2340180605) (.leaf 2279072254))) (.branch 35 (.branch 34 (.leaf 2219868392) (.leaf 2162496895)) (.branch 36 (.leaf 2106888911) (.leaf 2052978681)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2000703378) (.leaf 1950002955)) (.branch 40 (.leaf 1900820000) (.leaf 1853099599))) (.branch 43 (.branch 42 (.leaf 1806789211) (.leaf 1761838548)) (.branch 44 (.leaf 1718199462) (.leaf 1675825838))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1634673495) (.branch 47 (.leaf 1594700093) (.leaf 1555865039))) (.branch 50 (.branch 49 (.leaf 1518129409) (.leaf 1481455864)) (.branch 51 (.leaf 1445808577) (.leaf 1411153163)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1377456606) (.leaf 1344687203)) (.branch 55 (.leaf 1312814499) (.leaf 1281809231))) (.branch 58 (.branch 57 (.leaf 1251643275) (.leaf 1222289590)) (.branch 59 (.leaf 1193722177) (.leaf 1165916026))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1138847076) (.branch 62 (.leaf 1112492169) (.leaf 1086829018))) (.branch 65 (.branch 64 (.leaf 1061836160) (.leaf 1037492929)) (.branch 66 (.leaf 1013779413) (.leaf 990676432)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 968165496) (.leaf 946228785)) (.branch 70 (.leaf 924849117) (.leaf 904009920))) (.branch 73 (.branch 72 (.leaf 883695208) (.leaf 863889559)) (.branch 74 (.leaf 844578090) (.leaf 825746434))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 807380719) (.branch 77 (.leaf 789467553) (.leaf 771993996))) (.branch 80 (.branch 79 (.leaf 754947552) (.leaf 738316142)) (.branch 81 (.leaf 722088094) (.leaf 706252124)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 690797324) (.leaf 675713143)) (.branch 85 (.leaf 660989375) (.leaf 646616148))) (.branch 88 (.branch 87 (.leaf 632583908) (.leaf 618883410)) (.branch 89 (.leaf 605505703) (.leaf 592442120)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 579684272) (.branch 92 (.leaf 567224029) (.leaf 555053519))) (.branch 95 (.branch 94 (.leaf 543165111) (.leaf 531551414)) (.branch 96 (.leaf 520205260) (.leaf 509119704)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 498288009) (.leaf 487703643)) (.branch 100 (.leaf 477360271) (.leaf 467251745))) (.branch 103 (.branch 102 (.leaf 457372103) (.leaf 447715557)) (.branch 104 (.leaf 438276490) (.leaf 429049450))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 420029141) (.leaf 411210424)) (.branch 108 (.leaf 402588306) (.leaf 394157936))) (.branch 111 (.branch 110 (.leaf 385914604) (.leaf 377853730)) (.branch 112 (.leaf 369970866) (.leaf 362261688)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 354721992) (.leaf 347347691)) (.branch 116 (.leaf 340134812) (.leaf 333079490))) (.branch 119 (.branch 118 (.leaf 326177966) (.leaf 319426584)) (.branch 120 (.leaf 312821786) (.leaf 306360112)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 947).prefactor = (1198333471442417/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 947).cutoff/(generalMeanRows 947).c)).2 =
    (59675472313709/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 947).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 947).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 947).q*(generalMeanRows 947).c/2-2 = (79/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable007.value]
    have hcontinuation : (generalMeanRows 947).q*(generalMeanRows 947).cutoff/2-2 = (44/25:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable226.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 947).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 947

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 947).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 947).criticalRate j.val*(generalMeanRows 947).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 947).c*(generalMeanRows 947).criticalPoint j.val)).2-
      (generalMeanRows 947).J/2-(generalMeanRows 947).error (generalMeanGrid j.val)+
      (generalMeanRows 947).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 947).c)).2-
      (generalMeanRows 947).J/2-(generalMeanRows 947).error 4 := by
  have he : (generalMeanRows 947).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 947) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 947)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0947

/-! Kernel-checked entropy margins for general spectral rectangle 948. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0948
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5542733579) (.branch 2 (.leaf 5358351803) (.leaf 5181686853))) (.branch 5 (.branch 4 (.leaf 5012326642) (.leaf 4849887330)) (.branch 6 (.leaf 4694010835) (.leaf 4544362630)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4400629762) (.leaf 4262519093)) (.branch 10 (.leaf 4129755714) (.leaf 4002081521))) (.branch 13 (.branch 12 (.leaf 3879253923) (.leaf 3761044683)) (.branch 14 (.leaf 3647238860) (.leaf 3537633846))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3432038501) (.branch 17 (.leaf 3330272344) (.leaf 3232164833))) (.branch 20 (.branch 19 (.leaf 3137554690) (.leaf 3046289293)) (.branch 21 (.leaf 2958224107) (.leaf 2873222170)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2791153610) (.leaf 2711895207)) (.branch 25 (.leaf 2635329981) (.leaf 2561346814))) (.branch 28 (.branch 27 (.leaf 2489840100) (.leaf 2420709419)) (.branch 29 (.leaf 2353859233) (.leaf 2289198607)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2226640941) (.branch 32 (.leaf 2166103734) (.leaf 2107508346))) (.branch 35 (.branch 34 (.leaf 2050779791) (.leaf 1995846536)) (.branch 36 (.leaf 1942640312) (.leaf 1891095945)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1841151183) (.leaf 1792746551)) (.branch 40 (.leaf 1745825201) (.leaf 1700332779))) (.branch 43 (.branch 42 (.leaf 1656217296) (.leaf 1613429010)) (.branch 44 (.leaf 1571920310) (.leaf 1531645614))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1492561261) (.branch 47 (.leaf 1454625428) (.leaf 1417798029))) (.branch 50 (.branch 49 (.leaf 1382040637) (.leaf 1347316407)) (.branch 51 (.leaf 1313589992) (.leaf 1280827480)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1248996323) (.leaf 1218065275)) (.branch 55 (.leaf 1188004329) (.leaf 1158784664))) (.branch 58 (.branch 57 (.leaf 1130378586) (.leaf 1102759480)) (.branch 59 (.leaf 1075901763) (.leaf 1049780833))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1024373028) (.branch 62 (.leaf 999655583) (.leaf 975606595))) (.branch 65 (.branch 64 (.leaf 952204978) (.leaf 929430434)) (.branch 66 (.leaf 907263414) (.leaf 885685091)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 864677323) (.leaf 844222630)) (.branch 70 (.leaf 824304163) (.leaf 804905676))) (.branch 73 (.branch 72 (.leaf 786011504) (.leaf 767606537)) (.branch 74 (.leaf 749676199) (.leaf 732206423))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 715183634) (.branch 77 (.leaf 698594726) (.leaf 682427044))) (.branch 80 (.branch 79 (.leaf 666668366) (.leaf 651306887)) (.branch 81 (.leaf 636331201) (.leaf 621730285)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 607493485) (.leaf 593610501)) (.branch 85 (.leaf 580071374) (.leaf 566866472))) (.branch 88 (.branch 87 (.leaf 553986479) (.leaf 541422379)) (.branch 89 (.leaf 529165449) (.leaf 517207248)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 505539603) (.branch 92 (.leaf 494154599) (.leaf 483044575))) (.branch 95 (.branch 94 (.leaf 472202109) (.leaf 461620010)) (.branch 96 (.leaf 451291311) (.leaf 441209263)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 431367322) (.leaf 421759144)) (.branch 100 (.leaf 412378580) (.leaf 403219666))) (.branch 103 (.branch 102 (.leaf 394276617) (.leaf 385543823)) (.branch 104 (.leaf 377015840) (.leaf 368687385))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 360553334) (.leaf 352608709)) (.branch 108 (.leaf 344848680) (.leaf 337268557))) (.branch 111 (.branch 110 (.leaf 329863786) (.leaf 322629942)) (.branch 112 (.leaf 315562731) (.leaf 308657976)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 301911622) (.leaf 295319729)) (.branch 116 (.leaf 288878465) (.leaf 282584107))) (.branch 119 (.branch 118 (.leaf 276433035) (.leaf 270421729)) (.branch 120 (.leaf 264546768) (.leaf 258804823)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 948).prefactor = (239076994046497/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 948).cutoff/(generalMeanRows 948).c)).2 =
    (147712367807289/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 948).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 948).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 948).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 948

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 948).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 948).criticalRate j.val*(generalMeanRows 948).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 948).c*(generalMeanRows 948).criticalPoint j.val)).2-
      (generalMeanRows 948).J/2-(generalMeanRows 948).error (generalMeanGrid j.val)+
      (generalMeanRows 948).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 948).c)).2-
      (generalMeanRows 948).J/2-(generalMeanRows 948).error 4 := by
  have he : (generalMeanRows 948).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 948) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 948)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0948

/-! Kernel-checked entropy margins for general spectral rectangle 949. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0949
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5615581565) (.branch 2 (.leaf 5441651993) (.leaf 5274933816))) (.branch 5 (.branch 4 (.leaf 5115034797) (.leaf 4961589930)) (.branch 6 (.leaf 4814259041) (.leaf 4672724661)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4536690124) (.leaf 4405877862)) (.branch 10 (.leaf 4280027876) (.leaf 4158896355))) (.branch 13 (.branch 12 (.leaf 4042254432) (.leaf 3929887055)) (.branch 14 (.leaf 3821591967) (.leaf 3717178772))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3616468091) (.branch 17 (.leaf 3519290785) (.leaf 3425487248))) (.branch 20 (.branch 19 (.leaf 3334906760) (.leaf 3247406890)) (.branch 21 (.leaf 3162852949) (.leaf 3081117484)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3002079817) (.leaf 2925625614)) (.branch 25 (.leaf 2851646487) (.leaf 2780039628))) (.branch 28 (.branch 27 (.leaf 2710707467) (.leaf 2643557358)) (.branch 29 (.leaf 2578501285) (.leaf 2515455587)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2454340707) (.branch 32 (.leaf 2395080949) (.leaf 2337604267))) (.branch 35 (.branch 34 (.leaf 2281842049) (.leaf 2227728930)) (.branch 36 (.leaf 2175202609) (.leaf 2124203682)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2074675484) (.leaf 2026563941)) (.branch 40 (.leaf 1979817427) (.leaf 1934386642))) (.branch 43 (.branch 42 (.leaf 1890224483) (.leaf 1847285930)) (.branch 44 (.leaf 1805527940) (.leaf 1764909344))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1725390750) (.branch 47 (.leaf 1686934458) (.leaf 1649504367))) (.branch 50 (.branch 49 (.leaf 1613065900) (.leaf 1577585931)) (.branch 51 (.leaf 1543032705) (.leaf 1509375779)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1476585956) (.leaf 1444635222)) (.branch 55 (.leaf 1413496692) (.leaf 1383144557))) (.branch 58 (.branch 57 (.leaf 1353554030) (.leaf 1324701301)) (.branch 59 (.leaf 1296563491) (.leaf 1269118605))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1242345497) (.branch 62 (.leaf 1216223827) (.leaf 1190734027))) (.branch 65 (.branch 64 (.leaf 1165857263) (.leaf 1141575406)) (.branch 66 (.leaf 1117870997) (.leaf 1094727218)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1072127866) (.leaf 1050057323)) (.branch 70 (.leaf 1028500534) (.leaf 1007442979))) (.branch 73 (.branch 72 (.leaf 986870652) (.leaf 966770039)) (.branch 74 (.leaf 947128096) (.leaf 927932232))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 909170285) (.branch 77 (.leaf 890830510) (.leaf 872901558))) (.branch 80 (.branch 79 (.leaf 855372460) (.leaf 838232612)) (.branch 81 (.leaf 821471761) (.leaf 805079991)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 789047706) (.leaf 773365622)) (.branch 85 (.leaf 758024751) (.leaf 743016394))) (.branch 88 (.branch 87 (.leaf 728332122) (.leaf 713963774)) (.branch 89 (.leaf 699903441) (.leaf 686143458)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 672676396) (.branch 92 (.leaf 659495052) (.leaf 646592439))) (.branch 95 (.branch 94 (.leaf 633961780) (.leaf 621596500)) (.branch 96 (.leaf 609490219) (.leaf 597636744)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 586030059) (.leaf 574664328)) (.branch 100 (.leaf 563533876) (.leaf 552633195))) (.branch 103 (.branch 102 (.leaf 541956930) (.leaf 531499877)) (.branch 104 (.leaf 521256979) (.leaf 511223316))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 501394107) (.leaf 491764699)) (.branch 108 (.leaf 482330568) (.leaf 473087309))) (.branch 111 (.branch 110 (.leaf 464030637) (.leaf 455156381)) (.branch 112 (.leaf 446460481) (.leaf 437938982)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 429588035) (.leaf 421403888)) (.branch 116 (.leaf 413382887) (.leaf 405521473))) (.branch 119 (.branch 118 (.leaf 397816175) (.leaf 390263614)) (.branch 120 (.leaf 382860492) (.leaf 375603596)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 949).prefactor = (915778643706863/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 949).cutoff/(generalMeanRows 949).c)).2 =
    (71715289339683/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 949).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 949).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 949).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 949

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 949).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 949).criticalRate j.val*(generalMeanRows 949).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 949).c*(generalMeanRows 949).criticalPoint j.val)).2-
      (generalMeanRows 949).J/2-(generalMeanRows 949).error (generalMeanGrid j.val)+
      (generalMeanRows 949).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 949).c)).2-
      (generalMeanRows 949).J/2-(generalMeanRows 949).error 4 := by
  have he : (generalMeanRows 949).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 949) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 949)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0949

/-! Kernel-checked entropy margins for general spectral rectangle 950. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0950
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5471028831) (.branch 2 (.leaf 5300797823) (.leaf 5137672611))) (.branch 5 (.branch 4 (.leaf 4981263730) (.leaf 4831208853)) (.branch 6 (.leaf 4687170420) (.leaf 4548833509)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4415903946) (.leaf 4288106599)) (.branch 10 (.leaf 4165183858) (.leaf 4046894252))) (.branch 13 (.branch 12 (.leaf 3933011211) (.leaf 3823321938)) (.branch 14 (.leaf 3717626386) (.leaf 3615736329))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3517474517) (.branch 17 (.leaf 3422673898) (.leaf 3331176915))) (.branch 20 (.branch 19 (.leaf 3242834855) (.leaf 3157507253)) (.branch 21 (.leaf 3075061345) (.leaf 2995371564)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2918319078) (.leaf 2843791356)) (.branch 25 (.leaf 2771681772) (.leaf 2701889243))) (.branch 28 (.branch 27 (.leaf 2634317881) (.leaf 2568876684)) (.branch 29 (.leaf 2505479235) (.leaf 2444043438)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2384491257) (.branch 32 (.leaf 2326748482) (.leaf 2270744509))) (.branch 35 (.branch 34 (.leaf 2216412135) (.leaf 2163687361)) (.branch 36 (.leaf 2112509219) (.leaf 2062819598)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2014563090) (.leaf 1967686841)) (.branch 40 (.leaf 1922140414) (.leaf 1877875658))) (.branch 43 (.branch 42 (.leaf 1834846587) (.leaf 1793009264)) (.branch 44 (.leaf 1752321699) (.leaf 1712743740))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1674236983) (.branch 47 (.leaf 1636764682) (.leaf 1600291663))) (.branch 50 (.branch 49 (.leaf 1564784248) (.leaf 1530210176)) (.branch 51 (.leaf 1496538533) (.leaf 1463739688)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1431785230) (.leaf 1400647906)) (.branch 55 (.leaf 1370301564) (.leaf 1340721105))) (.branch 58 (.branch 57 (.leaf 1311882429) (.leaf 1283762389)) (.branch 59 (.leaf 1256338743) (.leaf 1229590118))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1203495963) (.branch 62 (.leaf 1178036514) (.leaf 1153192760))) (.branch 65 (.branch 64 (.leaf 1128946402) (.leaf 1105279829)) (.branch 66 (.leaf 1082176082) (.leaf 1059618824)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1037592316) (.leaf 1016081390)) (.branch 70 (.leaf 995071421) (.leaf 974548304))) (.branch 73 (.branch 72 (.leaf 954498436) (.leaf 934908688)) (.branch 74 (.leaf 915766391) (.leaf 897059310))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 878775630) (.branch 77 (.leaf 860903940) (.leaf 843433209))) (.branch 80 (.branch 79 (.leaf 826352780) (.leaf 809652345)) (.branch 81 (.leaf 793321939) (.leaf 777351919)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 761732958) (.leaf 746456027)) (.branch 85 (.leaf 731512384) (.leaf 716893565))) (.branch 88 (.branch 87 (.leaf 702591374) (.leaf 688597866)) (.branch 89 (.leaf 674905345) (.leaf 661506351)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 648393649) (.branch 92 (.leaf 635560225) (.leaf 622999275))) (.branch 95 (.branch 94 (.leaf 610704197) (.leaf 598668585)) (.branch 96 (.leaf 586886219) (.leaf 575351064)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564057255) (.leaf 552999098)) (.branch 100 (.leaf 542171061) (.leaf 531567769))) (.branch 103 (.branch 102 (.leaf 521183995) (.leaf 511014662)) (.branch 104 (.leaf 501054832) (.leaf 491299701))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 481744598) (.leaf 472384980)) (.branch 108 (.leaf 463216424) (.leaf 454234627))) (.branch 111 (.branch 110 (.leaf 445435399) (.leaf 436814663)) (.branch 112 (.leaf 428368447) (.leaf 420092884)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 411984206) (.leaf 404038744)) (.branch 116 (.leaf 396252920) (.leaf 388623250))) (.branch 119 (.branch 118 (.leaf 381146337) (.leaf 373818869)) (.branch 120 (.leaf 366637617) (.leaf 359599434)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 950).prefactor = (1137639340474171/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 950).cutoff/(generalMeanRows 950).c)).2 =
    (46065371366913/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 950).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 950).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 950).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 950

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 950).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 950).criticalRate j.val*(generalMeanRows 950).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 950).c*(generalMeanRows 950).criticalPoint j.val)).2-
      (generalMeanRows 950).J/2-(generalMeanRows 950).error (generalMeanGrid j.val)+
      (generalMeanRows 950).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 950).c)).2-
      (generalMeanRows 950).J/2-(generalMeanRows 950).error 4 := by
  have he : (generalMeanRows 950).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 950) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 950)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0950

/-! Kernel-checked entropy margins for general spectral rectangle 951. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0951
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5245925999) (.branch 2 (.leaf 5079950985) (.leaf 4920973020))) (.branch 5 (.branch 4 (.leaf 4768605868) (.leaf 4622490306)) (.branch 6 (.leaf 4482291762) (.leaf 4347698204)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4218418251) (.leaf 4094179482)) (.branch 10 (.leaf 3974726915) (.leaf 3859821636))) (.branch 13 (.branch 12 (.leaf 3749239561) (.leaf 3642770308)) (.branch 14 (.leaf 3540216185) (.leaf 3441391258))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3346120508) (.branch 17 (.leaf 3254239055) (.leaf 3165591458))) (.branch 20 (.branch 19 (.leaf 3080031063) (.leaf 2997419411)) (.branch 21 (.leaf 2917625690) (.leaf 2840526232)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2766004050) (.leaf 2693948410)) (.branch 25 (.leaf 2624254435) (.leaf 2556822735))) (.branch 28 (.branch 27 (.leaf 2491559074) (.leaf 2428374049)) (.branch 29 (.leaf 2367182799) (.leaf 2307904736)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2250463288) (.branch 32 (.leaf 2194785664) (.leaf 2140802639))) (.branch 35 (.branch 34 (.leaf 2088448341) (.leaf 2037660066)) (.branch 36 (.leaf 1988378096) (.leaf 1940545535)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1894108146) (.leaf 1849014213)) (.branch 40 (.leaf 1805214396) (.leaf 1762661609))) (.branch 43 (.branch 42 (.leaf 1721310892) (.leaf 1681119304)) (.branch 44 (.leaf 1642045813) (.leaf 1604051195))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1567097944) (.branch 47 (.leaf 1531150179) (.leaf 1496173562))) (.branch 50 (.branch 49 (.leaf 1462135222) (.leaf 1429003676)) (.branch 51 (.leaf 1396748765) (.leaf 1365341582)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1334754415) (.leaf 1304960687)) (.branch 55 (.leaf 1275934898) (.leaf 1247652578))) (.branch 58 (.branch 57 (.leaf 1220090231) (.leaf 1193225294)) (.branch 59 (.leaf 1167036091) (.leaf 1141501789))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1116602361) (.branch 62 (.leaf 1092318549) (.leaf 1068631827))) (.branch 65 (.branch 64 (.leaf 1045524366) (.leaf 1022979006)) (.branch 66 (.leaf 1000979223) (.leaf 979509101)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 958553305) (.leaf 938097057)) (.branch 70 (.leaf 918126108) (.leaf 898626716))) (.branch 73 (.branch 72 (.leaf 879585627) (.leaf 860990050)) (.branch 74 (.leaf 842827638) (.leaf 825086471))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 807755038) (.branch 77 (.leaf 790822216) (.leaf 774277259))) (.branch 80 (.branch 79 (.leaf 758109777) (.leaf 742309727)) (.branch 81 (.leaf 726867396) (.leaf 711773385)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 697018601) (.leaf 682594244)) (.branch 85 (.leaf 668491793) (.leaf 654702995))) (.branch 88 (.branch 87 (.leaf 641219859) (.leaf 628034640)) (.branch 89 (.leaf 615139833) (.leaf 602528163)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 590192577) (.branch 92 (.leaf 578126234) (.leaf 566322498))) (.branch 95 (.branch 94 (.leaf 554774931) (.leaf 543477285)) (.branch 96 (.leaf 532423494) (.leaf 521607670)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 511024095) (.leaf 500667215)) (.branch 100 (.leaf 490531632) (.leaf 480612104))) (.branch 103 (.branch 102 (.leaf 470903534) (.leaf 461400968)) (.branch 104 (.leaf 452099590) (.leaf 442994715))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 434081788) (.leaf 425356375)) (.branch 108 (.leaf 416814166) (.leaf 408450962))) (.branch 111 (.branch 110 (.leaf 400262679) (.leaf 392245340)) (.branch 112 (.leaf 384395073) (.leaf 376708107)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 369180769) (.leaf 361809482)) (.branch 116 (.leaf 354590760) (.leaf 347521206))) (.branch 119 (.branch 118 (.leaf 340597511) (.leaf 333816446)) (.branch 120 (.leaf 327174868) (.leaf 320669709)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 951).prefactor = (1128839811126191/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 951).cutoff/(generalMeanRows 951).c)).2 =
    (186380540845187/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 951).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 951).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 951).q*(generalMeanRows 951).c/2-2 = (31/40:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable307.value]
    have hcontinuation : (generalMeanRows 951).q*(generalMeanRows 951).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 951).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 951

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 951).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 951).criticalRate j.val*(generalMeanRows 951).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 951).c*(generalMeanRows 951).criticalPoint j.val)).2-
      (generalMeanRows 951).J/2-(generalMeanRows 951).error (generalMeanGrid j.val)+
      (generalMeanRows 951).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 951).c)).2-
      (generalMeanRows 951).J/2-(generalMeanRows 951).error 4 := by
  have he : (generalMeanRows 951).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 951) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 951)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0951

/-! Kernel-checked entropy margins for general spectral rectangle 952. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0952
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5081888866) (.branch 2 (.leaf 4912499886) (.leaf 4750367350))) (.branch 5 (.branch 4 (.leaf 4595091700) (.leaf 4446301208)) (.branch 6 (.leaf 4303649536) (.leaf 4166813569)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4035491473) (.leaf 3909400960)) (.branch 10 (.leaf 3788277715) (.leaf 3671873997))) (.branch 13 (.branch 12 (.leaf 3559957353) (.leaf 3452309473)) (.branch 14 (.leaf 3348725135) (.leaf 3249011256))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3152986019) (.branch 17 (.leaf 3060478081) (.leaf 2971325844))) (.branch 20 (.branch 19 (.leaf 2885376793) (.leaf 2802486880)) (.branch 21 (.leaf 2722519964) (.leaf 2645347291)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2570847022) (.leaf 2498903785)) (.branch 25 (.leaf 2429408271) (.leaf 2362256858))) (.branch 28 (.branch 27 (.leaf 2297351258) (.leaf 2234598193)) (.branch 29 (.leaf 2173909096) (.leaf 2115199828)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2058390418) (.branch 32 (.leaf 2003404823) (.leaf 1950170696))) (.branch 35 (.branch 34 (.leaf 1898619178) (.leaf 1848684700)) (.branch 36 (.leaf 1800304799) (.leaf 1753419946)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1707973380) (.leaf 1663910963)) (.branch 40 (.leaf 1621181034) (.leaf 1579734277))) (.branch 43 (.branch 42 (.leaf 1539523597) (.leaf 1500504000)) (.branch 44 (.leaf 1462632488) (.leaf 1425867949))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1390171063) (.branch 47 (.leaf 1355504213) (.leaf 1321831392))) (.branch 50 (.branch 49 (.leaf 1289118127) (.leaf 1257331401)) (.branch 51 (.leaf 1226439578) (.leaf 1196412339)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1167220615) (.leaf 1138836526)) (.branch 55 (.leaf 1111233324) (.leaf 1084385341))) (.branch 58 (.branch 57 (.leaf 1058267934) (.leaf 1032857437)) (.branch 59 (.leaf 1008131117) (.leaf 984067131))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 960644482) (.branch 62 (.leaf 937842980) (.leaf 915643209))) (.branch 65 (.branch 64 (.leaf 894026488) (.leaf 872974839)) (.branch 66 (.leaf 852470956) (.leaf 832498176)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 813040447) (.leaf 794082304)) (.branch 70 (.leaf 775608846) (.leaf 757605703))) (.branch 73 (.branch 72 (.leaf 740059024) (.leaf 722955446)) (.branch 74 (.leaf 706282077) (.leaf 690026478))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 674176639) (.branch 77 (.leaf 658720966) (.leaf 643648261))) (.branch 80 (.branch 79 (.leaf 628947707) (.leaf 614608851)) (.branch 81 (.leaf 600621591) (.leaf 586976161)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 573663118) (.leaf 560673327)) (.branch 85 (.leaf 547997954) (.leaf 535628447))) (.branch 88 (.branch 87 (.leaf 523556532) (.leaf 511774199)) (.branch 89 (.leaf 500273690) (.leaf 489047492)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 478088329) (.branch 92 (.leaf 467389150) (.leaf 456943121))) (.branch 95 (.branch 94 (.leaf 446743620) (.leaf 436784224)) (.branch 96 (.leaf 427058707) (.leaf 417561031)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 408285337) (.leaf 399225940)) (.branch 100 (.leaf 390377325) (.leaf 381734139))) (.branch 103 (.branch 102 (.leaf 373291183) (.leaf 365043412)) (.branch 104 (.leaf 356985925) (.leaf 349113962))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 341422900) (.leaf 333908246)) (.branch 108 (.leaf 326565634) (.leaf 319390821))) (.branch 111 (.branch 110 (.leaf 312379683) (.leaf 305528209)) (.branch 112 (.leaf 298832502) (.leaf 292288768)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 285893320) (.leaf 279642570)) (.branch 116 (.leaf 273533028) (.leaf 267561297))) (.branch 119 (.branch 118 (.leaf 261724072) (.leaf 256018136)) (.branch 120 (.leaf 250440357) (.leaf 244987687)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 952).prefactor = (2326434335766609/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 952).cutoff/(generalMeanRows 952).c)).2 =
    (346092834608211/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 952).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 952).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 952).q*(generalMeanRows 952).c/2-2 = (17/20:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable055.value]
    have hcontinuation : (generalMeanRows 952).q*(generalMeanRows 952).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 952).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 952

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 952).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 952).criticalRate j.val*(generalMeanRows 952).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 952).c*(generalMeanRows 952).criticalPoint j.val)).2-
      (generalMeanRows 952).J/2-(generalMeanRows 952).error (generalMeanGrid j.val)+
      (generalMeanRows 952).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 952).c)).2-
      (generalMeanRows 952).J/2-(generalMeanRows 952).error 4 := by
  have he : (generalMeanRows 952).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 952) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 952)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0952

/-! Kernel-checked entropy margins for general spectral rectangle 953. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0953
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5256976859) (.branch 2 (.leaf 5090409067) (.leaf 4930902467))) (.branch 5 (.branch 4 (.leaf 4778064025) (.leaf 4631528347)) (.branch 6 (.leaf 4490955265) (.leaf 4356027667)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4226449573) (.leaf 4101944398)) (.branch 10 (.leaf 3982253394) (.leaf 3867134243))) (.branch 13 (.branch 12 (.leaf 3756359788) (.leaf 3649716881)) (.branch 14 (.leaf 3547005338) (.leaf 3448036986))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3352634796) (.branch 17 (.leaf 3260632094) (.leaf 3171871829))) (.branch 20 (.branch 19 (.leaf 3086205918) (.leaf 3003494629)) (.branch 21 (.leaf 2923606021) (.leaf 2846415433)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2771805001) (.leaf 2699663224)) (.branch 25 (.leaf 2629884555) (.leaf 2562369027))) (.branch 28 (.branch 27 (.leaf 2497021903) (.leaf 2433753357)) (.branch 29 (.leaf 2372478167) (.leaf 2313115445)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2255588371) (.branch 32 (.leaf 2199823958) (.leaf 2145752821))) (.branch 35 (.branch 34 (.leaf 2093308972) (.leaf 2042429622)) (.branch 36 (.leaf 1993055001) (.leaf 1945128183)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1898594930) (.leaf 1853403542)) (.branch 40 (.leaf 1809504714) (.leaf 1766851411))) (.branch 43 (.branch 42 (.leaf 1725398737) (.leaf 1685103826)) (.branch 44 (.leaf 1645925730) (.leaf 1607825321))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1570765190) (.branch 47 (.leaf 1534709561) (.leaf 1499624206))) (.branch 50 (.branch 49 (.leaf 1465476364) (.leaf 1432234667)) (.branch 51 (.leaf 1399869070) (.leaf 1368350782)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1337652206) (.leaf 1307746879)) (.branch 55 (.leaf 1278609413) (.leaf 1250215448))) (.branch 58 (.branch 57 (.leaf 1222541598) (.leaf 1195565407)) (.branch 59 (.leaf 1169265299) (.leaf 1143620543))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1118611209) (.branch 62 (.leaf 1094218131) (.leaf 1070422871))) (.branch 65 (.branch 64 (.leaf 1047207689) (.leaf 1024555505)) (.branch 66 (.leaf 1002449873) (.leaf 980874951)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 959815475) (.leaf 939256732)) (.branch 70 (.leaf 919184536) (.leaf 899585203))) (.branch 73 (.branch 72 (.leaf 880445534) (.leaf 861752788)) (.branch 74 (.leaf 843494666) (.leaf 825659293))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 808235195) (.branch 77 (.leaf 791211286) (.leaf 774576855))) (.branch 80 (.branch 79 (.leaf 758321541) (.leaf 742435327)) (.branch 81 (.leaf 726908524) (.leaf 711731754)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 696895943) (.leaf 682392304)) (.branch 85 (.leaf 668212329) (.leaf 654347776))) (.branch 88 (.branch 87 (.leaf 640790661) (.leaf 627533243)) (.branch 89 (.leaf 614568022) (.leaf 601887722)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 589485290) (.branch 92 (.leaf 577353882) (.leaf 565486856))) (.branch 95 (.branch 94 (.leaf 553877768) (.leaf 542520362)) (.branch 96 (.leaf 531408563) (.leaf 520536470)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 509898353) (.leaf 499488644)) (.branch 100 (.leaf 489301930) (.leaf 479332954))) (.branch 103 (.branch 102 (.leaf 469576600) (.leaf 460027898)) (.branch 104 (.leaf 450682010) (.leaf 441534234))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 432579992) (.leaf 423814831)) (.branch 108 (.leaf 415234416) (.leaf 406834528))) (.branch 111 (.branch 110 (.leaf 398611059) (.leaf 390560008)) (.branch 112 (.leaf 382677480) (.leaf 374959678)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 367402906) (.leaf 360003562)) (.branch 116 (.leaf 352758133) (.leaf 345663199))) (.branch 119 (.branch 118 (.leaf 338715424) (.leaf 331911554)) (.branch 120 (.leaf 325248420) (.leaf 318722928)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 953).prefactor = (1151018293736541/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 953).cutoff/(generalMeanRows 953).c)).2 =
    (48124726017351/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 953).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 953).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 953).q*(generalMeanRows 953).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 953).q*(generalMeanRows 953).cutoff/2-2 = (889/425:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable310.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 953).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 953

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 953).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 953).criticalRate j.val*(generalMeanRows 953).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 953).c*(generalMeanRows 953).criticalPoint j.val)).2-
      (generalMeanRows 953).J/2-(generalMeanRows 953).error (generalMeanGrid j.val)+
      (generalMeanRows 953).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 953).c)).2-
      (generalMeanRows 953).J/2-(generalMeanRows 953).error 4 := by
  have he : (generalMeanRows 953).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 953) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 953)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0953

/-! Kernel-checked entropy margins for general spectral rectangle 954. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0954
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5244255379) (.branch 2 (.leaf 5073619048) (.leaf 4910274156))) (.branch 5 (.branch 4 (.leaf 4753815463) (.leaf 4603866168)) (.branch 6 (.leaf 4460075416) (.leaf 4322116078)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4189682768) (.leaf 4062490059)) (.branch 10 (.leaf 3940270879) (.leaf 3822775074))) (.branch 13 (.branch 12 (.leaf 3709768090) (.leaf 3601029799)) (.branch 14 (.leaf 3496353420) (.leaf 3395544542))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3298420230) (.branch 17 (.leaf 3204808216) (.leaf 3114546148))) (.branch 20 (.branch 19 (.leaf 3027480909) (.leaf 2943467991)) (.branch 21 (.leaf 2862370917) (.leaf 2784060711)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2708415409) (.leaf 2635319605)) (.branch 25 (.leaf 2564664036) (.leaf 2496345194))) (.branch 28 (.branch 27 (.leaf 2430264967) (.leaf 2366330310)) (.branch 29 (.leaf 2304452934) (.leaf 2244549019)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2186538951) (.branch 32 (.leaf 2130347069) (.leaf 2075901437))) (.branch 35 (.branch 34 (.leaf 2023133628) (.leaf 1971978521)) (.branch 36 (.leaf 1922374115) (.leaf 1874261350)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1827583948) (.leaf 1782288253)) (.branch 40 (.leaf 1738323091) (.leaf 1695639632))) (.branch 43 (.branch 42 (.leaf 1654191265) (.leaf 1613933481)) (.branch 44 (.leaf 1574823755) (.leaf 1536821449))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1499887706) (.branch 47 (.leaf 1463985362) (.leaf 1429078858))) (.branch 50 (.branch 49 (.leaf 1395134157) (.leaf 1362118667)) (.branch 51 (.leaf 1330001167) (.leaf 1298751739)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1268341706) (.leaf 1238743567)) (.branch 55 (.leaf 1209930938) (.leaf 1181878505))) (.branch 58 (.branch 57 (.leaf 1154561963) (.leaf 1127957976)) (.branch 59 (.leaf 1102044124) (.leaf 1076798864))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1052201488) (.branch 62 (.leaf 1028232082) (.leaf 1004871492))) (.branch 65 (.branch 64 (.leaf 982101287) (.leaf 959903728)) (.branch 66 (.leaf 938261734) (.leaf 917158854)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 896579240) (.leaf 876507616)) (.branch 70 (.leaf 856929259) (.leaf 837829970))) (.branch 73 (.branch 72 (.leaf 819196052) (.leaf 801014290)) (.branch 74 (.leaf 783271928) (.leaf 765956653))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 749056573) (.branch 77 (.leaf 732560199) (.leaf 716456433))) (.branch 80 (.branch 79 (.leaf 700734547) (.leaf 685384168)) (.branch 81 (.leaf 670395267) (.leaf 655758142)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 641463407) (.leaf 627501976)) (.branch 85 (.leaf 613865057) (.leaf 600544135))) (.branch 88 (.branch 87 (.leaf 587530962) (.leaf 574817550)) (.branch 89 (.leaf 562396158) (.leaf 550259284)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 538399654) (.branch 92 (.leaf 526810216) (.leaf 515484132))) (.branch 95 (.branch 94 (.leaf 504414765) (.leaf 493595680)) (.branch 96 (.leaf 483020628) (.leaf 472683546)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 462578545) (.leaf 452699909)) (.branch 100 (.leaf 443042085) (.leaf 433599678))) (.branch 103 (.branch 102 (.leaf 424367449) (.leaf 415340302)) (.branch 104 (.leaf 406513288) (.leaf 397881594))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 389440541) (.leaf 381185576)) (.branch 108 (.leaf 373112274) (.leaf 365216330))) (.branch 111 (.branch 110 (.leaf 357493552) (.leaf 349939864)) (.branch 112 (.leaf 342551298) (.leaf 335323992)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 328254184) (.leaf 321338213)) (.branch 116 (.leaf 314572513) (.leaf 307953610))) (.branch 119 (.branch 118 (.leaf 301478123) (.leaf 295142754)) (.branch 120 (.leaf 288944292) (.leaf 282879608)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 954).prefactor = (1184488337737983/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 954).cutoff/(generalMeanRows 954).c)).2 =
    (371796296280273/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 954).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 954).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 954).q*(generalMeanRows 954).cutoff/2-2 = (889/425:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable310.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 954).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 954

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 954).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 954).criticalRate j.val*(generalMeanRows 954).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 954).c*(generalMeanRows 954).criticalPoint j.val)).2-
      (generalMeanRows 954).J/2-(generalMeanRows 954).error (generalMeanGrid j.val)+
      (generalMeanRows 954).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 954).c)).2-
      (generalMeanRows 954).J/2-(generalMeanRows 954).error 4 := by
  have he : (generalMeanRows 954).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 954) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 954)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0954

/-! Kernel-checked entropy margins for general spectral rectangle 955. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0955
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5314001397) (.branch 2 (.leaf 5138845450) (.leaf 4971205039))) (.branch 5 (.branch 4 (.leaf 4810662712) (.leaf 4656830277)) (.branch 6 (.leaf 4509346246) (.leaf 4367873543)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4232097471) (.leaf 4101723871)) (.branch 10 (.leaf 3976477481) (.leaf 3856100447))) (.branch 13 (.branch 12 (.leaf 3740350977) (.leaf 3629002129)) (.branch 14 (.leaf 3521840699) (.leaf 3418666220))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3319290043) (.branch 17 (.leaf 3223534499) (.leaf 3131232132))) (.branch 20 (.branch 19 (.leaf 3042224998) (.leaf 2956364018)) (.branch 21 (.leaf 2873508386) (.leaf 2793525021)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2716288067) (.leaf 2641678426)) (.branch 25 (.leaf 2569583325) (.leaf 2499895926))) (.branch 28 (.branch 27 (.leaf 2432514951) (.leaf 2367344342)) (.branch 29 (.leaf 2304292945) (.leaf 2243274213)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2184205934) (.branch 32 (.leaf 2127009974) (.leaf 2071612039))) (.branch 35 (.branch 34 (.leaf 2017941452) (.leaf 1965930949)) (.branch 36 (.leaf 1915516482) (.leaf 1866637040)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1819234478) (.leaf 1773253360)) (.branch 40 (.leaf 1728640810) (.leaf 1685346373))) (.branch 43 (.branch 42 (.leaf 1643321883) (.leaf 1602521343)) (.branch 44 (.leaf 1562900808) (.leaf 1524418277))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1487033592) (.branch 47 (.leaf 1450708342) (.leaf 1415405776))) (.branch 50 (.branch 49 (.leaf 1381090713) (.leaf 1347729465)) (.branch 51 (.leaf 1315289762) (.leaf 1283740683)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1253052585) (.leaf 1223197042)) (.branch 55 (.leaf 1194146787) (.leaf 1165875654))) (.branch 58 (.branch 57 (.leaf 1138358525) (.leaf 1111571280)) (.branch 59 (.leaf 1085490750) (.leaf 1060094672))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1035361646) (.branch 62 (.leaf 1011271096) (.leaf 987803230))) (.branch 65 (.branch 64 (.leaf 964939007) (.leaf 942660099)) (.branch 66 (.leaf 920948863) (.leaf 899788305)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 879162057) (.leaf 859054345)) (.branch 70 (.leaf 839449963) (.leaf 820334253))) (.branch 73 (.branch 72 (.leaf 801693074) (.leaf 783512784)) (.branch 74 (.leaf 765780220) (.leaf 748482675))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 731607877) (.branch 77 (.leaf 715143977) (.leaf 699079526))) (.branch 80 (.branch 79 (.leaf 683403459) (.leaf 668105083)) (.branch 81 (.leaf 653174058) (.leaf 638600384)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 624374387) (.leaf 610486710)) (.branch 85 (.leaf 596928292) (.leaf 583690365))) (.branch 88 (.branch 87 (.leaf 570764437) (.leaf 558142285)) (.branch 89 (.leaf 545815943) (.leaf 533777690)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 522020045) (.branch 92 (.leaf 510535757) (.leaf 499317792))) (.branch 95 (.branch 94 (.leaf 488359332) (.leaf 477653761)) (.branch 96 (.leaf 467194661) (.leaf 456975805)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 446991147) (.leaf 437234820)) (.branch 100 (.leaf 427701125) (.leaf 418384528))) (.branch 103 (.branch 102 (.leaf 409279657) (.leaf 400381287)) (.branch 104 (.leaf 391684346) (.leaf 383183904))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 374875166) (.leaf 366753474)) (.branch 108 (.leaf 358814297) (.leaf 351053229))) (.branch 111 (.branch 110 (.leaf 343465985) (.leaf 336048396)) (.branch 112 (.leaf 328796406) (.leaf 321706069)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 314773543) (.leaf 307995090)) (.branch 116 (.leaf 301367070) (.leaf 294885940))) (.branch 119 (.branch 118 (.leaf 288548249) (.leaf 282350637)) (.branch 120 (.leaf 276289831) (.leaf 270362642)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 955).prefactor = (975145316019403/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 955).cutoff/(generalMeanRows 955).c)).2 =
    (182630162650243/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 955).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 955).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 955).q*(generalMeanRows 955).c/2-2 = (3359/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable311.value]
    have hcontinuation : (generalMeanRows 955).q*(generalMeanRows 955).cutoff/2-2 = (889/425:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable310.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 955).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 955

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 955).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 955).criticalRate j.val*(generalMeanRows 955).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 955).c*(generalMeanRows 955).criticalPoint j.val)).2-
      (generalMeanRows 955).J/2-(generalMeanRows 955).error (generalMeanGrid j.val)+
      (generalMeanRows 955).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 955).c)).2-
      (generalMeanRows 955).J/2-(generalMeanRows 955).error 4 := by
  have he : (generalMeanRows 955).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 955) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 955)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0955

/-! Kernel-checked entropy margins for general spectral rectangle 956. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0956
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5385004445) (.branch 2 (.leaf 5205238432) (.leaf 5033218382))) (.branch 5 (.branch 4 (.leaf 4868514244) (.leaf 4710726078)) (.branch 6 (.leaf 4559481419) (.leaf 4414432933)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4275256312) (.leaf 4141648392)) (.branch 10 (.leaf 4013325457) (.leaf 3890021710))) (.branch 13 (.branch 12 (.leaf 3771487892) (.leaf 3657490026)) (.branch 14 (.leaf 3547808285) (.leaf 3442235954))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3340578487) (.branch 17 (.leaf 3242652646) (.leaf 3148285710))) (.branch 20 (.branch 19 (.leaf 3057314754) (.leaf 2969585986)) (.branch 21 (.leaf 2884954134) (.leaf 2803281886)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2724439373) (.leaf 2648303688)) (.branch 25 (.leaf 2574758444) (.leaf 2503693369))) (.branch 28 (.branch 27 (.leaf 2435003920) (.leaf 2368590936)) (.branch 29 (.leaf 2304360313) (.leaf 2242222694)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2182093192) (.branch 32 (.leaf 2123891124) (.leaf 2067539771))) (.branch 35 (.branch 34 (.leaf 2012966141) (.leaf 1960100764)) (.branch 36 (.leaf 1908877486) (.leaf 1859233288)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1811108108) (.leaf 1764444679)) (.branch 40 (.leaf 1719188376) (.leaf 1675287074))) (.branch 43 (.branch 42 (.leaf 1632691010) (.leaf 1591352660)) (.branch 44 (.leaf 1551226619) (.leaf 1512269490))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1474439781) (.branch 47 (.leaf 1437697803) (.leaf 1402005579))) (.branch 50 (.branch 49 (.leaf 1367326757) (.leaf 1333626530)) (.branch 51 (.leaf 1300871552) (.leaf 1269029874)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1238070865) (.leaf 1207965157)) (.branch 55 (.leaf 1178684577) (.leaf 1150202089))) (.branch 58 (.branch 57 (.leaf 1122491744) (.leaf 1095528624)) (.branch 59 (.leaf 1069288794) (.leaf 1043749258))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1018887912) (.branch 62 (.leaf 994683502) (.leaf 971115590))) (.branch 65 (.branch 64 (.leaf 948164511) (.leaf 925811342)) (.branch 66 (.leaf 904037864) (.leaf 882826536)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 862160460) (.leaf 842023355)) (.branch 70 (.leaf 822399530) (.leaf 803273857))) (.branch 73 (.branch 72 (.leaf 784631748) (.leaf 766459129)) (.branch 74 (.leaf 748742424) (.leaf 731468527))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 714624786) (.branch 77 (.leaf 698198984) (.leaf 682179320))) (.branch 80 (.branch 79 (.leaf 666554392) (.leaf 651313181)) (.branch 81 (.leaf 636445035) (.leaf 621939655)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 607787079) (.leaf 593977673)) (.branch 85 (.leaf 580502112) (.leaf 567351371))) (.branch 88 (.branch 87 (.leaf 554516716) (.leaf 541989686)) (.branch 89 (.leaf 529762091) (.leaf 517825993)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 506173704) (.branch 92 (.leaf 494797771) (.leaf 483690970))) (.branch 95 (.branch 94 (.leaf 472846298) (.leaf 462256964)) (.branch 96 (.leaf 451916379) (.leaf 441818154)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 431956088) (.leaf 422324162)) (.branch 100 (.leaf 412916536) (.leaf 403727538))) (.branch 103 (.branch 102 (.leaf 394751662) (.leaf 385983560)) (.branch 104 (.leaf 377418037) (.leaf 369050046))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 360874682) (.leaf 352887181)) (.branch 108 (.leaf 345082909) (.leaf 337457363))) (.branch 111 (.branch 110 (.leaf 330006164) (.leaf 322725054)) (.branch 112 (.leaf 315609893) (.leaf 308656650)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 301861408) (.leaf 295220353)) (.branch 116 (.leaf 288729775) (.leaf 282386061))) (.branch 119 (.branch 118 (.leaf 276185696) (.leaf 270125259)) (.branch 120 (.leaf 264201416) (.leaf 258410924)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 956).prefactor = (501750606706337/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 956).cutoff/(generalMeanRows 956).c)).2 =
    (358766795989939/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 956).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 956).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 956).q*(generalMeanRows 956).c/2-2 = (3433/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable312.value]
    have hcontinuation : (generalMeanRows 956).q*(generalMeanRows 956).cutoff/2-2 = (889/425:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable310.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 956).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 956

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 956).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 956).criticalRate j.val*(generalMeanRows 956).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 956).c*(generalMeanRows 956).criticalPoint j.val)).2-
      (generalMeanRows 956).J/2-(generalMeanRows 956).error (generalMeanGrid j.val)+
      (generalMeanRows 956).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 956).c)).2-
      (generalMeanRows 956).J/2-(generalMeanRows 956).error 4 := by
  have he : (generalMeanRows 956).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 956) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 956)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0956

/-! Kernel-checked entropy margins for general spectral rectangle 957. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0957
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5541593038) (.branch 2 (.leaf 5356599675) (.leaf 5179577516))) (.branch 5 (.branch 4 (.leaf 5010084006) (.leaf 4847707575)) (.branch 6 (.leaf 4692064927) (.leaf 4542798629)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4399574941) (.leaf 4262081885)) (.branch 10 (.leaf 4130027494) (.leaf 4003138243))) (.branch 13 (.branch 12 (.leaf 3881157622) (.leaf 3763844853)) (.branch 14 (.leaf 3650973716) (.leaf 3542331486))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3437717959) (.branch 17 (.leaf 3336944568) (.leaf 3239833569))) (.branch 20 (.branch 19 (.leaf 3146217302) (.leaf 3055937501)) (.branch 21 (.leaf 2968844670) (.leaf 2884797505)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2803662359) (.leaf 2725312751)) (.branch 25 (.leaf 2649628912) (.leaf 2576497361))) (.branch 28 (.branch 27 (.leaf 2505810516) (.leaf 2437466334)) (.branch 29 (.leaf 2371367972) (.leaf 2307423475)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2245545489) (.branch 32 (.leaf 2185650985) (.leaf 2127661011))) (.branch 35 (.branch 34 (.leaf 2071500454) (.leaf 2017097824)) (.branch 36 (.leaf 1964385043) (.leaf 1913297259)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1863772664) (.leaf 1815752327)) (.branch 40 (.leaf 1769180032) (.leaf 1724002140))) (.branch 43 (.branch 42 (.leaf 1680167440) (.leaf 1637627027)) (.branch 44 (.leaf 1596334176) (.leaf 1556244227))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1517314482) (.branch 47 (.leaf 1479504096) (.leaf 1442773991))) (.branch 50 (.branch 49 (.leaf 1407086757) (.leaf 1372406573)) (.branch 51 (.leaf 1338699125) (.leaf 1305931534)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1274072280) (.leaf 1243091139)) (.branch 55 (.leaf 1212959119) (.leaf 1183648399))) (.branch 58 (.branch 57 (.leaf 1155132275) (.leaf 1127385104)) (.branch 59 (.leaf 1100382256) (.leaf 1074100065))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1048515784) (.branch 62 (.leaf 1023607543) (.leaf 999354308))) (.branch 65 (.branch 64 (.leaf 975735844) (.leaf 952732674)) (.branch 66 (.leaf 930326054) (.leaf 908497929)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 887230912) (.leaf 866508248)) (.branch 70 (.leaf 846313788) (.leaf 826631967))) (.branch 73 (.branch 72 (.leaf 807447770) (.leaf 788746717)) (.branch 74 (.leaf 770514834) (.leaf 752738635))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 735405101) (.branch 77 (.leaf 718501659) (.leaf 702016165))) (.branch 80 (.branch 79 (.leaf 685936886) (.leaf 670252481)) (.branch 81 (.leaf 654951989) (.leaf 640024812)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 625460700) (.leaf 611249735)) (.branch 85 (.leaf 597382322) (.leaf 583849176))) (.branch 88 (.branch 87 (.leaf 570641306) (.leaf 557750008)) (.branch 89 (.leaf 545166851) (.leaf 532883668)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 520892546) (.branch 92 (.leaf 509185816) (.leaf 497756045))) (.branch 95 (.branch 94 (.leaf 486596025) (.leaf 475698767)) (.branch 96 (.leaf 465057492) (.leaf 454665624)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 444516782) (.leaf 434604774)) (.branch 100 (.leaf 424923586) (.leaf 415467385))) (.branch 103 (.branch 102 (.leaf 406230503) (.leaf 397207436)) (.branch 104 (.leaf 388392839) (.leaf 379781518))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 371368426) (.leaf 363148659)) (.branch 108 (.leaf 355117450) (.leaf 347270163))) (.branch 111 (.branch 110 (.leaf 339602294) (.leaf 332109459)) (.branch 112 (.leaf 324787398) (.leaf 317631965)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 310639127) (.leaf 303804959)) (.branch 116 (.leaf 297125643) (.leaf 290597463))) (.branch 119 (.branch 118 (.leaf 284216800) (.leaf 277980133)) (.branch 120 (.leaf 271884033) (.leaf 265925161)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 957).prefactor = (16135650963659/3125000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 957).cutoff/(generalMeanRows 957).c)).2 =
    (358766795989939/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 957).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 957).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 957).q*(generalMeanRows 957).c/2-2 = (3433/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable312.value]
    have hcontinuation : (generalMeanRows 957).q*(generalMeanRows 957).cutoff/2-2 = (889/425:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable310.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 957).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 957

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 957).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 957).criticalRate j.val*(generalMeanRows 957).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 957).c*(generalMeanRows 957).criticalPoint j.val)).2-
      (generalMeanRows 957).J/2-(generalMeanRows 957).error (generalMeanGrid j.val)+
      (generalMeanRows 957).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 957).c)).2-
      (generalMeanRows 957).J/2-(generalMeanRows 957).error 4 := by
  have he : (generalMeanRows 957).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 957) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 957)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0957

/-! Kernel-checked entropy margins for general spectral rectangle 958. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0958
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7670921288) (.branch 2 (.leaf 7456215783) (.leaf 7249694343))) (.branch 5 (.branch 4 (.leaf 7050937348) (.leaf 6859553965)) (.branch 6 (.leaf 6675179542) (.leaf 6497473297)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6326116273) (.leaf 6160809506)) (.branch 10 (.leaf 6001272396) (.leaf 5847241238))) (.branch 13 (.branch 12 (.leaf 5698467909) (.leaf 5554718677)) (.branch 14 (.leaf 5415773134) (.leaf 5281423215))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5151472324) (.branch 17 (.leaf 5025734525) (.leaf 4904033813))) (.branch 20 (.branch 19 (.leaf 4786203442) (.leaf 4672085314)) (.branch 21 (.leaf 4561529413) (.leaf 4454393296)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4350541609) (.leaf 4249845654)) (.branch 25 (.leaf 4152182983) (.leaf 4057437022))) (.branch 28 (.branch 27 (.leaf 3965496729) (.leaf 3876256267)) (.branch 29 (.leaf 3789614707) (.leaf 3705475755)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3623747488) (.branch 32 (.leaf 3544342117) (.leaf 3467175759))) (.branch 35 (.branch 34 (.leaf 3392168232) (.leaf 3319242855)) (.branch 36 (.leaf 3248326264) (.leaf 3179348245)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3112241568) (.leaf 3046941836)) (.branch 40 (.leaf 2983387345) (.leaf 2921518951))) (.branch 43 (.branch 42 (.leaf 2861279940) (.leaf 2802615913)) (.branch 44 (.leaf 2745474676) (.leaf 2689806129))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2635562173) (.branch 47 (.leaf 2582696613) (.leaf 2531165068))) (.branch 50 (.branch 49 (.leaf 2480924891) (.leaf 2431935088)) (.branch 51 (.leaf 2384156242) (.leaf 2337550445)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2292081225) (.leaf 2247713489)) (.branch 55 (.leaf 2204413459) (.leaf 2162148612))) (.branch 58 (.branch 57 (.leaf 2120887632) (.leaf 2080600352)) (.branch 59 (.leaf 2041257707) (.leaf 2002831688))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1965295298) (.branch 62 (.leaf 1928622506) (.leaf 1892788210))) (.branch 65 (.branch 64 (.leaf 1857768198) (.leaf 1823539109)) (.branch 66 (.leaf 1790078403) (.leaf 1757364321)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1725375861) (.leaf 1694092739)) (.branch 70 (.leaf 1663495369) (.leaf 1633564829))) (.branch 73 (.branch 72 (.leaf 1604282836) (.leaf 1575631724)) (.branch 74 (.leaf 1547594416) (.leaf 1520154403))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1493295721) (.branch 77 (.leaf 1467002931) (.leaf 1441261098))) (.branch 80 (.branch 79 (.leaf 1416055775) (.leaf 1391372977)) (.branch 81 (.leaf 1367199173) (.leaf 1343521261)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1320326556) (.leaf 1297602775)) (.branch 85 (.leaf 1275338019) (.leaf 1253520763))) (.branch 88 (.branch 87 (.leaf 1232139838) (.leaf 1211184420)) (.branch 89 (.leaf 1190644018) (.leaf 1170508463)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1150767892) (.branch 92 (.leaf 1131412742) (.leaf 1112433736))) (.branch 95 (.branch 94 (.leaf 1093821875) (.leaf 1075568426)) (.branch 96 (.leaf 1057664916) (.leaf 1040103118)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1022875047) (.leaf 1005972951)) (.branch 100 (.leaf 989389298) (.leaf 973116777))) (.branch 103 (.branch 102 (.leaf 957148281) (.leaf 941476909)) (.branch 104 (.leaf 926095951) (.leaf 910998889))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 896179384) (.leaf 881631274)) (.branch 108 (.leaf 867348567) (.leaf 853325435))) (.branch 111 (.branch 110 (.leaf 839556210) (.leaf 826035377)) (.branch 112 (.leaf 812757570) (.leaf 799717566)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 786910283) (.leaf 774330772)) (.branch 116 (.leaf 761974215) (.leaf 749835922))) (.branch 119 (.branch 118 (.leaf 737911323) (.leaf 726195966)) (.branch 120 (.leaf 714685517) (.leaf 703375751)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 958).prefactor = (623590550165171/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 958).cutoff/(generalMeanRows 958).c)).2 =
    (373677546371/1250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 958).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 958).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 958).q*(generalMeanRows 958).cutoff/2-2 = (40/27:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable223.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 958).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 958

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 958).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 958).criticalRate j.val*(generalMeanRows 958).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 958).c*(generalMeanRows 958).criticalPoint j.val)).2-
      (generalMeanRows 958).J/2-(generalMeanRows 958).error (generalMeanGrid j.val)+
      (generalMeanRows 958).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 958).c)).2-
      (generalMeanRows 958).J/2-(generalMeanRows 958).error 4 := by
  have he : (generalMeanRows 958).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 958) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 958)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0958

/-! Kernel-checked entropy margins for general spectral rectangle 959. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0959
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7142904615) (.branch 2 (.leaf 6929698027) (.leaf 6724774801))) (.branch 5 (.branch 4 (.leaf 6527710054) (.leaf 6338107933)) (.branch 6 (.leaf 6155599002) (.leaf 5979837926)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5810501408) (.leaf 5647286354)) (.branch 10 (.leaf 5489908229) (.leaf 5338099587))) (.branch 13 (.branch 12 (.leaf 5191608737) (.leaf 5050198555)) (.branch 14 (.leaf 4913645398) (.leaf 4781738123))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4654277200) (.branch 17 (.leaf 4531073899) (.leaf 4411949551))) (.branch 20 (.branch 19 (.leaf 4296734871) (.leaf 4185269340)) (.branch 21 (.leaf 4077400635) (.leaf 3972984108)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3871882304) (.leaf 3773964521)) (.branch 25 (.leaf 3679106395) (.leaf 3587189523))) (.branch 28 (.branch 27 (.leaf 3498101114) (.leaf 3411733664)) (.branch 29 (.leaf 3327984648) (.leaf 3246756246)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3167955076) (.branch 32 (.leaf 3091491953) (.leaf 3017281659))) (.branch 35 (.branch 34 (.leaf 2945242734) (.leaf 2875297272)) (.branch 36 (.leaf 2807370738) (.leaf 2741391795)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2677292137) (.leaf 2615006337)) (.branch 40 (.leaf 2554471702) (.leaf 2495628140))) (.branch 43 (.branch 42 (.leaf 2438418028) (.leaf 2382786097)) (.branch 44 (.leaf 2328679314) (.leaf 2276046777))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2224839616) (.branch 47 (.leaf 2175010896) (.leaf 2126515526))) (.branch 50 (.branch 49 (.leaf 2079310176) (.leaf 2033353198)) (.branch 51 (.leaf 1988604543) (.leaf 1945025698)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1902579611) (.leaf 1861230630)) (.branch 55 (.leaf 1820944437) (.leaf 1781687997))) (.branch 58 (.branch 57 (.leaf 1743429494) (.leaf 1706138284)) (.branch 59 (.leaf 1669784846) (.leaf 1634340728))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1599778508) (.branch 62 (.leaf 1566071749) (.leaf 1533194956))) (.branch 65 (.branch 64 (.leaf 1501123539) (.leaf 1469833778)) (.branch 66 (.leaf 1439302781) (.leaf 1409508457)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1380429479) (.leaf 1352045259)) (.branch 70 (.leaf 1324335910) (.leaf 1297282226))) (.branch 73 (.branch 72 (.leaf 1270865651) (.leaf 1245068256)) (.branch 74 (.leaf 1219872710) (.leaf 1195262264))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1171220720) (.branch 77 (.leaf 1147732419) (.leaf 1124782211))) (.branch 80 (.branch 79 (.leaf 1102355444) (.leaf 1080437940)) (.branch 81 (.leaf 1059015978) (.leaf 1038076278)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1017605986) (.leaf 997592653)) (.branch 85 (.leaf 978024226) (.leaf 958889030))) (.branch 88 (.branch 87 (.leaf 940175755) (.leaf 921873442)) (.branch 89 (.leaf 903971474) (.leaf 886459557)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 869327715) (.branch 92 (.leaf 852566274) (.leaf 836165856))) (.branch 95 (.branch 94 (.leaf 820117362) (.leaf 804411969)) (.branch 96 (.leaf 789041116) (.leaf 773996496)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 759270048) (.leaf 744853947)) (.branch 100 (.leaf 730740598) (.leaf 716922625))) (.branch 103 (.branch 102 (.leaf 703392868) (.leaf 690144372)) (.branch 104 (.leaf 677170380) (.leaf 664464328))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 652019841) (.leaf 639830720)) (.branch 108 (.leaf 627890942) (.leaf 616194652))) (.branch 111 (.branch 110 (.leaf 604736159) (.leaf 593509926)) (.branch 112 (.leaf 582510571) (.leaf 571732860)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 561171700) (.leaf 550822136)) (.branch 116 (.leaf 540679347) (.leaf 530738642))) (.branch 119 (.branch 118 (.leaf 520995456) (.leaf 511445343)) (.branch 120 (.leaf 502083976) (.leaf 492907143)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 959).prefactor = (1258646067554269/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 959).cutoff/(generalMeanRows 959).c)).2 =
    (13660639556549/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 959).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 959).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 959).q*(generalMeanRows 959).c/2-2 = (271/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable076.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 959).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 959

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 959).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 959).criticalRate j.val*(generalMeanRows 959).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 959).c*(generalMeanRows 959).criticalPoint j.val)).2-
      (generalMeanRows 959).J/2-(generalMeanRows 959).error (generalMeanGrid j.val)+
      (generalMeanRows 959).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 959).c)).2-
      (generalMeanRows 959).J/2-(generalMeanRows 959).error 4 := by
  have he : (generalMeanRows 959).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 959) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 959)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0959

/-! Kernel-checked entropy margins for general spectral rectangle 960. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0960
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7103293009) (.branch 2 (.leaf 6901601109) (.leaf 6707763529))) (.branch 5 (.branch 4 (.leaf 6521371016) (.leaf 6342042404)) (.branch 6 (.leaf 6169422100) (.leaf 6003177856)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5842998782) (.leaf 5688593576)) (.branch 10 (.leaf 5539688937) (.leaf 5396028139))) (.branch 13 (.branch 12 (.leaf 5257369750) (.leaf 5123486473)) (.branch 14 (.leaf 4994164100) (.leaf 4869200557))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4748405045) (.branch 17 (.leaf 4631597247) (.leaf 4518606614))) (.branch 20 (.branch 19 (.leaf 4409271704) (.leaf 4303439582)) (.branch 21 (.leaf 4200965263) (.leaf 4101711206)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4005546845) (.leaf 3912348153)) (.branch 25 (.leaf 3821997247) (.leaf 3734382017))) (.branch 28 (.branch 27 (.leaf 3649395781) (.leaf 3566936970)) (.branch 29 (.leaf 3486908828) (.leaf 3409219145)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3333779995) (.branch 32 (.leaf 3260507497) (.leaf 3189321597))) (.branch 35 (.branch 34 (.leaf 3120145859) (.leaf 3052907268)) (.branch 36 (.leaf 2987536048) (.leaf 2923965496)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2862131818) (.leaf 2801973980)) (.branch 40 (.leaf 2743433567) (.leaf 2686454653))) (.branch 43 (.branch 42 (.leaf 2630983671) (.leaf 2576969304)) (.branch 44 (.leaf 2524362364) (.leaf 2473115698))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2423184085) (.branch 47 (.leaf 2374524140) (.leaf 2327094235))) (.branch 50 (.branch 49 (.leaf 2280854409) (.leaf 2235766292)) (.branch 51 (.leaf 2191793032) (.leaf 2148899224)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2107050844) (.leaf 2066215186)) (.branch 55 (.leaf 2026360804) (.leaf 1987457452))) (.branch 58 (.branch 57 (.leaf 1949476032) (.leaf 1912388547)) (.branch 59 (.leaf 1876168046) (.leaf 1840788583))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1806225172) (.branch 62 (.leaf 1772453745) (.leaf 1739451113))) (.branch 65 (.branch 64 (.leaf 1707194928) (.leaf 1675663649)) (.branch 66 (.leaf 1644836507) (.leaf 1614693470)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1585215219) (.leaf 1556383110)) (.branch 70 (.leaf 1528179152) (.leaf 1500585980))) (.branch 73 (.branch 72 (.leaf 1473586826) (.leaf 1447165499)) (.branch 74 (.leaf 1421306357) (.leaf 1395994289))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1371214693) (.branch 77 (.leaf 1346953456) (.leaf 1323196930))) (.branch 80 (.branch 79 (.leaf 1299931922) (.leaf 1277145670)) (.branch 81 (.leaf 1254825827) (.leaf 1232960449)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1211537974) (.leaf 1190547211)) (.branch 85 (.leaf 1169977324) (.leaf 1149817821))) (.branch 88 (.branch 87 (.leaf 1130058538) (.leaf 1110689629)) (.branch 89 (.leaf 1091701551) (.leaf 1073085058)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1054831186) (.branch 92 (.leaf 1036931242) (.leaf 1019376797))) (.branch 95 (.branch 94 (.leaf 1002159677) (.leaf 985271948)) (.branch 96 (.leaf 968705914) (.leaf 952454104)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 936509268) (.leaf 920864365)) (.branch 100 (.leaf 905512558) (.leaf 890447205))) (.branch 103 (.branch 102 (.leaf 875661856) (.leaf 861150242)) (.branch 104 (.leaf 846906271) (.leaf 832924021))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 819197737) (.leaf 805721820)) (.branch 108 (.leaf 792490825) (.leaf 779499458))) (.branch 111 (.branch 110 (.leaf 766742566) (.leaf 754215136)) (.branch 112 (.leaf 741912289) (.leaf 729829274)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 717961469) (.leaf 706304369)) (.branch 116 (.leaf 694853590) (.leaf 683604861))) (.branch 119 (.branch 118 (.leaf 672554018) (.leaf 661697008)) (.branch 120 (.leaf 651029878) (.leaf 640548776)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 960).prefactor = (4851681621371429/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 960).cutoff/(generalMeanRows 960).c)).2 =
    (323662084905763/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 960).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 960).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 960).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 960

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 960).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 960).criticalRate j.val*(generalMeanRows 960).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 960).c*(generalMeanRows 960).criticalPoint j.val)).2-
      (generalMeanRows 960).J/2-(generalMeanRows 960).error (generalMeanGrid j.val)+
      (generalMeanRows 960).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 960).c)).2-
      (generalMeanRows 960).J/2-(generalMeanRows 960).error 4 := by
  have he : (generalMeanRows 960).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 960) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 960)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0960

/-! Kernel-checked entropy margins for general spectral rectangle 961. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0961
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6684888017) (.branch 2 (.leaf 6485746176) (.leaf 6294482416))) (.branch 5 (.branch 4 (.leaf 6110685256) (.leaf 5933971402)) (.branch 6 (.leaf 5763983238) (.leaf 5600386593)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5442868756) (.leaf 5291136704)) (.branch 10 (.leaf 5144915508) (.leaf 5003946910))) (.branch 13 (.branch 12 (.leaf 4867988035) (.leaf 4736810228)) (.branch 14 (.leaf 4610198006) (.leaf 4487948098))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4369868581) (.branch 17 (.leaf 4255778086) (.leaf 4145505078))) (.branch 20 (.branch 19 (.leaf 4038887193) (.leaf 3935770631)) (.branch 21 (.leaf 3836009600) (.leaf 3739465805)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3646007974) (.leaf 3555511423)) (.branch 25 (.leaf 3467857654) (.leaf 3382933982))) (.branch 28 (.branch 27 (.leaf 3300633191) (.leaf 3220853213)) (.branch 29 (.leaf 3143496827) (.leaf 3068471388)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2995688566) (.branch 32 (.leaf 2925064104) (.leaf 2856517598))) (.branch 35 (.branch 34 (.leaf 2789972284) (.leaf 2725354841)) (.branch 36 (.leaf 2662595212) (.leaf 2601626429)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2542384452) (.leaf 2484808018)) (.branch 40 (.leaf 2428838501) (.leaf 2374419773))) (.branch 43 (.branch 42 (.leaf 2321498086) (.leaf 2270021948)) (.branch 44 (.leaf 2219942013) (.leaf 2171210979))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2123783484) (.branch 47 (.leaf 2077616016) (.leaf 2032666827))) (.branch 50 (.branch 49 (.leaf 1988895841) (.leaf 1946264587)) (.branch 51 (.leaf 1904736113) (.leaf 1864274926)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1824846916) (.leaf 1786419300)) (.branch 55 (.leaf 1748960556) (.leaf 1712440371))) (.branch 58 (.branch 57 (.leaf 1676829586) (.leaf 1642100141)) (.branch 59 (.leaf 1608225033) (.leaf 1575178263))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1542934798) (.branch 62 (.leaf 1511470525) (.leaf 1480762215))) (.branch 65 (.branch 64 (.leaf 1450787481) (.leaf 1421524747)) (.branch 66 (.leaf 1392953210) (.leaf 1365052811)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1337804198) (.leaf 1311188705)) (.branch 70 (.leaf 1285188316) (.leaf 1259785645))) (.branch 73 (.branch 72 (.leaf 1234963904) (.leaf 1210706882)) (.branch 74 (.leaf 1186998924) (.leaf 1163824904))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1141170206) (.branch 77 (.leaf 1119020706) (.leaf 1097362747))) (.branch 80 (.branch 79 (.leaf 1076183126) (.leaf 1055469076)) (.branch 81 (.leaf 1035208244) (.leaf 1015388682)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 995998825) (.leaf 977027480)) (.branch 85 (.leaf 958463812) (.leaf 940297329))) (.branch 88 (.branch 87 (.leaf 922517870) (.leaf 905115591)) (.branch 89 (.leaf 888080957) (.leaf 871404726)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 855077939) (.branch 92 (.leaf 839091915) (.leaf 823438233))) (.branch 95 (.branch 94 (.leaf 808108728) (.leaf 793095480)) (.branch 96 (.leaf 778390805) (.leaf 763987246)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 749877567) (.leaf 736054744)) (.branch 100 (.leaf 722511957) (.leaf 709242583))) (.branch 103 (.branch 102 (.leaf 696240191) (.leaf 683498532)) (.branch 104 (.leaf 671011537) (.leaf 658773306))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 646778106) (.leaf 635020365)) (.branch 108 (.leaf 623494663) (.leaf 612195732))) (.branch 111 (.branch 110 (.leaf 601118448) (.leaf 590257826)) (.branch 112 (.leaf 579609017) (.leaf 569167301)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 558928087) (.leaf 548886905)) (.branch 116 (.leaf 539039403) (.leaf 529381345))) (.branch 119 (.branch 118 (.leaf 519908603) (.leaf 510617160)) (.branch 120 (.leaf 501503101) (.leaf 492562612)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 961).prefactor = (4866174079650257/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 961).cutoff/(generalMeanRows 961).c)).2 =
    (154572400178521/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 961).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 961).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 961).q*(generalMeanRows 961).c/2-2 = (673/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable313.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 961).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 961

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 961).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 961).criticalRate j.val*(generalMeanRows 961).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 961).c*(generalMeanRows 961).criticalPoint j.val)).2-
      (generalMeanRows 961).J/2-(generalMeanRows 961).error (generalMeanGrid j.val)+
      (generalMeanRows 961).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 961).c)).2-
      (generalMeanRows 961).J/2-(generalMeanRows 961).error 4 := by
  have he : (generalMeanRows 961).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 961) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 961)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0961

/-! Kernel-checked entropy margins for general spectral rectangle 962. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0962
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6331405018) (.branch 2 (.leaf 6135543495) (.leaf 5947551574))) (.branch 5 (.branch 4 (.leaf 5767016490) (.leaf 5593553729)) (.branch 6 (.leaf 5426804516) (.leaf 5266433586)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5112127205) (.leaf 4963591390)) (.branch 10 (.leaf 4820550326) (.leaf 4682744931))) (.branch 13 (.branch 12 (.leaf 4549931572) (.leaf 4421880899)) (.branch 14 (.leaf 4298376792) (.leaf 4179215404))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4064204287) (.branch 17 (.leaf 3953161603) (.leaf 3845915394))) (.branch 20 (.branch 19 (.leaf 3742302921) (.leaf 3642170053)) (.branch 21 (.leaf 3545370708) (.leaf 3451766339)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3361225457) (.leaf 3273623197)) (.branch 25 (.leaf 3188840911) (.leaf 3106765792))) (.branch 28 (.branch 27 (.leaf 3027290529) (.leaf 2950312983)) (.branch 29 (.leaf 2875735889) (.leaf 2803466577)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2733416709) (.branch 32 (.leaf 2665502043) (.leaf 2599642202))) (.branch 35 (.branch 34 (.leaf 2535760468) (.leaf 2473783577)) (.branch 36 (.leaf 2413641544) (.leaf 2355267482)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2298597445) (.leaf 2243570270)) (.branch 40 (.leaf 2190127442) (.leaf 2138212952))) (.branch 43 (.branch 42 (.leaf 2087773175) (.leaf 2038756751)) (.branch 44 (.leaf 1991114469) (.leaf 1944799168))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1899765630) (.branch 47 (.leaf 1855970492) (.leaf 1813372155))) (.branch 50 (.branch 49 (.leaf 1771930699) (.leaf 1731607807)) (.branch 51 (.leaf 1692366685) (.leaf 1654171998)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1616989796) (.leaf 1580787456)) (.branch 55 (.leaf 1545533617) (.leaf 1511198127))) (.branch 58 (.branch 57 (.leaf 1477751987) (.leaf 1445167299)) (.branch 59 (.leaf 1413417218) (.leaf 1382475907))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1352318489) (.branch 62 (.leaf 1322921012) (.leaf 1294260401))) (.branch 65 (.branch 64 (.leaf 1266314428) (.leaf 1239061669)) (.branch 66 (.leaf 1212481475) (.leaf 1186553939)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1161259862) (.leaf 1136580724)) (.branch 70 (.leaf 1112498660) (.leaf 1088996427))) (.branch 73 (.branch 72 (.leaf 1066057384) (.leaf 1043665465)) (.branch 74 (.leaf 1021805154) (.leaf 1000461467))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 979619926) (.branch 77 (.leaf 959266544) (.leaf 939387802))) (.branch 80 (.branch 79 (.leaf 919970630) (.leaf 901002394)) (.branch 81 (.leaf 882470872) (.leaf 864364246)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 846671081) (.leaf 829380310)) (.branch 85 (.leaf 812481224) (.leaf 795963455))) (.branch 88 (.branch 87 (.leaf 779816966) (.leaf 764032035)) (.branch 89 (.leaf 748599247) (.leaf 733509480)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 718753894) (.branch 92 (.leaf 704323923) (.leaf 690211263))) (.branch 95 (.branch 94 (.leaf 676407865) (.leaf 662905922)) (.branch 96 (.leaf 649697861) (.leaf 636776340)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 624134232) (.leaf 611764624)) (.branch 100 (.leaf 599660803) (.leaf 587816256))) (.branch 103 (.branch 102 (.leaf 576224658) (.leaf 564879867)) (.branch 104 (.leaf 553775919) (.leaf 542907020))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 532267539) (.leaf 521852009)) (.branch 108 (.leaf 511655112) (.leaf 501671682))) (.branch 111 (.branch 110 (.leaf 491896696) (.leaf 482325269)) (.branch 112 (.leaf 472952653) (.leaf 463774228)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 454785499) (.leaf 445982097)) (.branch 116 (.leaf 437359765) (.leaf 428914365))) (.branch 119 (.branch 118 (.leaf 420641868) (.leaf 412538349)) (.branch 120 (.leaf 404599991) (.leaf 396823075)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 962).prefactor = (4868596027148149/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 962).cutoff/(generalMeanRows 962).c)).2 =
    (75078680227193/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 962).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 962).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 962).q*(generalMeanRows 962).c/2-2 = (73/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable024.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 962).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 962

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 962).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 962).criticalRate j.val*(generalMeanRows 962).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 962).c*(generalMeanRows 962).criticalPoint j.val)).2-
      (generalMeanRows 962).J/2-(generalMeanRows 962).error (generalMeanGrid j.val)+
      (generalMeanRows 962).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 962).c)).2-
      (generalMeanRows 962).J/2-(generalMeanRows 962).error 4 := by
  have he : (generalMeanRows 962).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 962) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 962)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0962

/-! Kernel-checked entropy margins for general spectral rectangle 963. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0963
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5944986245) (.branch 2 (.leaf 5753316526) (.leaf 5569489244))) (.branch 5 (.branch 4 (.leaf 5393090992) (.leaf 5223736624)) (.branch 6 (.leaf 5061066757) (.leaf 4904745550)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4754458725) (.leaf 4609911796)) (.branch 10 (.leaf 4470828482) (.leaf 4336949278))) (.branch 13 (.branch 12 (.leaf 4208030169) (.leaf 4083841465)) (.branch 14 (.leaf 3964166746) (.leaf 3848801905))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3737554272) (.branch 17 (.leaf 3630241825) (.leaf 3526692455))) (.branch 20 (.branch 19 (.leaf 3426743307) (.leaf 3330240165)) (.branch 21 (.leaf 3237036893) (.leaf 3146994915)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3059982744) (.leaf 2975875538)) (.branch 25 (.leaf 2894554696) (.leaf 2815907479))) (.branch 28 (.branch 27 (.leaf 2739826664) (.leaf 2666210219)) (.branch 29 (.leaf 2594961000) (.leaf 2525986475)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2459198459) (.branch 32 (.leaf 2394512875) (.leaf 2331849524))) (.branch 35 (.branch 34 (.leaf 2271131872) (.leaf 2212286855)) (.branch 36 (.leaf 2155244691) (.leaf 2099938707)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2046305176) (.leaf 1994283164)) (.branch 40 (.leaf 1943814383) (.leaf 1894843062))) (.branch 43 (.branch 42 (.leaf 1847315816) (.leaf 1801181527)) (.branch 44 (.leaf 1756391232) (.leaf 1712898016))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1670656913) (.branch 47 (.leaf 1629624812) (.leaf 1589760365))) (.branch 50 (.branch 49 (.leaf 1551023908) (.leaf 1513377376)) (.branch 51 (.leaf 1476784230) (.leaf 1441209389)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1406619156) (.leaf 1372981160)) (.branch 55 (.leaf 1340264294) (.leaf 1308438656))) (.branch 58 (.branch 57 (.leaf 1277475496) (.leaf 1247347165)) (.branch 59 (.leaf 1218027065) (.leaf 1189489604))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1161710150) (.branch 62 (.leaf 1134664991) (.leaf 1108331293))) (.branch 65 (.branch 64 (.leaf 1082687065) (.leaf 1057711121)) (.branch 66 (.leaf 1033383046) (.leaf 1009683164)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 986592506) (.leaf 964092781)) (.branch 70 (.leaf 942166350) (.leaf 920796193))) (.branch 73 (.branch 72 (.leaf 899965892) (.leaf 879659599)) (.branch 74 (.leaf 859862016) (.leaf 840558374))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 821734410) (.branch 77 (.leaf 803376347) (.leaf 785470874))) (.branch 80 (.branch 79 (.leaf 768005131) (.leaf 750966687)) (.branch 81 (.leaf 734343524) (.leaf 718124025)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 702296953) (.leaf 686851441)) (.branch 85 (.leaf 671776974) (.leaf 657063378))) (.branch 88 (.branch 87 (.leaf 642700808) (.leaf 628679732)) (.branch 89 (.leaf 614990922) (.leaf 601625443)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 588574642) (.branch 92 (.leaf 575830135) (.leaf 563383799))) (.branch 95 (.branch 94 (.leaf 551227766) (.leaf 539354405)) (.branch 96 (.leaf 527756324) (.leaf 516426353)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 505357541) (.leaf 494543145)) (.branch 100 (.leaf 483976625) (.leaf 473651637))) (.branch 103 (.branch 102 (.leaf 463562024) (.leaf 453701811)) (.branch 104 (.leaf 444065200) (.leaf 434646559))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 425440423) (.leaf 416441484)) (.branch 108 (.leaf 407644585) (.leaf 399044720))) (.branch 111 (.branch 110 (.leaf 390637023) (.leaf 382416767)) (.branch 112 (.leaf 374379357) (.leaf 366520329)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 358835342) (.leaf 351320177)) (.branch 116 (.leaf 343970730) (.leaf 336783011))) (.branch 119 (.branch 118 (.leaf 329753140) (.leaf 322877342)) (.branch 120 (.leaf 316151944) (.leaf 309573373)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 963).prefactor = (4859984962732511/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 963).cutoff/(generalMeanRows 963).c)).2 =
    (9051794576087/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 963).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 963).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 963).q*(generalMeanRows 963).c/2-2 = (6357/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable270.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 963).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 963

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 963).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 963).criticalRate j.val*(generalMeanRows 963).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 963).c*(generalMeanRows 963).criticalPoint j.val)).2-
      (generalMeanRows 963).J/2-(generalMeanRows 963).error (generalMeanGrid j.val)+
      (generalMeanRows 963).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 963).c)).2-
      (generalMeanRows 963).J/2-(generalMeanRows 963).error 4 := by
  have he : (generalMeanRows 963).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 963) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 963)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0963

/-! Kernel-checked entropy margins for general spectral rectangle 964. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0964
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5703000902) (.branch 2 (.leaf 5515353478) (.leaf 5335481627))) (.branch 5 (.branch 4 (.leaf 5162972773) (.leaf 4997442571)) (.branch 6 (.leaf 4838532419) (.leaf 4685907248)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4539253548) (.leaf 4398277602)) (.branch 10 (.leaf 4262703902) (.leaf 4132273722))) (.branch 13 (.branch 12 (.leaf 4006743835) (.leaf 3885885346)) (.branch 14 (.leaf 3769482640) (.leaf 3657332423))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3549242848) (.branch 17 (.leaf 3445032719) (.leaf 3344530766))) (.branch 20 (.branch 19 (.leaf 3247574974) (.leaf 3154011973)) (.branch 21 (.leaf 3063696477) (.leaf 2976490762)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2892264195) (.leaf 2810892788)) (.branch 25 (.leaf 2732258790) (.leaf 2656250316))) (.branch 28 (.branch 27 (.leaf 2582760988) (.leaf 2511689619)) (.branch 29 (.leaf 2442939905) (.leaf 2376420145)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2312042984) (.branch 32 (.leaf 2249725162) (.leaf 2189387292))) (.branch 35 (.branch 34 (.leaf 2130953644) (.leaf 2074351947)) (.branch 36 (.leaf 2019513205) (.leaf 1966371519)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1914863925) (.leaf 1864930242)) (.branch 40 (.leaf 1816512926) (.leaf 1769556935))) (.branch 43 (.branch 42 (.leaf 1724009603) (.leaf 1679820518)) (.branch 44 (.leaf 1636941414) (.leaf 1595326057))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1554930153) (.branch 47 (.leaf 1515711247) (.leaf 1477628639))) (.branch 50 (.branch 49 (.leaf 1440643296) (.leaf 1404717776)) (.branch 51 (.leaf 1369816149) (.leaf 1335903927)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1302948000) (.leaf 1270916569)) (.branch 55 (.leaf 1239779085) (.leaf 1209506194))) (.branch 58 (.branch 57 (.leaf 1180069683) (.leaf 1151442426)) (.branch 59 (.leaf 1123598340) (.leaf 1096512333))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1070160262) (.branch 62 (.leaf 1044518896) (.leaf 1019565869))) (.branch 65 (.branch 64 (.leaf 995279647) (.leaf 971639491)) (.branch 66 (.leaf 948625423) (.leaf 926218193)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 904399250) (.leaf 883150709)) (.branch 70 (.leaf 862455328) (.leaf 842296476))) (.branch 73 (.branch 72 (.leaf 822658113) (.leaf 803524762)) (.branch 74 (.leaf 784881486) (.leaf 766713870))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 749007993) (.branch 77 (.leaf 731750415) (.leaf 714928154))) (.branch 80 (.branch 79 (.leaf 698528671) (.leaf 682539846)) (.branch 81 (.leaf 666949969) (.leaf 651747721)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 636922155) (.leaf 622462690)) (.branch 85 (.leaf 608359088) (.leaf 594601448))) (.branch 88 (.branch 87 (.leaf 581180188) (.leaf 568086037)) (.branch 89 (.leaf 555310019) (.leaf 542843447)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 530677908) (.branch 92 (.leaf 518805255) (.leaf 507217596))) (.branch 95 (.branch 94 (.leaf 495907287) (.leaf 484866921)) (.branch 96 (.leaf 474089317) (.leaf 463567518)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 453294778) (.leaf 443264557)) (.branch 100 (.leaf 433470511) (.leaf 423906488))) (.branch 103 (.branch 102 (.leaf 414566521) (.leaf 405444819)) (.branch 104 (.leaf 396535764) (.leaf 387833901))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 379333939) (.leaf 371030738)) (.branch 108 (.leaf 362919309) (.leaf 354994806))) (.branch 111 (.branch 110 (.leaf 347252523) (.leaf 339687889)) (.branch 112 (.leaf 332296463) (.leaf 325073929)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 318016094) (.leaf 311118882)) (.branch 116 (.leaf 304378330) (.leaf 297790588))) (.branch 119 (.branch 118 (.leaf 291351909) (.leaf 285058653)) (.branch 120 (.leaf 278907277) (.leaf 272894336)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 964).prefactor = (2420675945520867/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 964).cutoff/(generalMeanRows 964).c)).2 =
    (7279972187519/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 964).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 964).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 964).q*(generalMeanRows 964).c/2-2 = (331/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable296.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 964).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 964

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 964).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 964).criticalRate j.val*(generalMeanRows 964).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 964).c*(generalMeanRows 964).criticalPoint j.val)).2-
      (generalMeanRows 964).J/2-(generalMeanRows 964).error (generalMeanGrid j.val)+
      (generalMeanRows 964).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 964).c)).2-
      (generalMeanRows 964).J/2-(generalMeanRows 964).error 4 := by
  have he : (generalMeanRows 964).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 964) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 964)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0964

/-! Kernel-checked entropy margins for general spectral rectangle 965. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0965
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5754169406) (.branch 2 (.leaf 5578005634) (.leaf 5409076011))) (.branch 5 (.branch 4 (.leaf 5246989319) (.leaf 5091381456)) (.branch 6 (.leaf 4941913049) (.leaf 4798267325)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4660148222) (.leaf 4527278689)) (.branch 10 (.leaf 4399399160) (.leaf 4276266181))) (.branch 13 (.branch 12 (.leaf 4157651173) (.leaf 4043339305)) (.branch 14 (.leaf 3933128480) (.leaf 3826828408))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3724259761) (.branch 17 (.leaf 3625253407) (.leaf 3529649703))) (.branch 20 (.branch 19 (.leaf 3437297851) (.leaf 3348055306)) (.branch 21 (.leaf 3261787232) (.leaf 3178366001)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3097670730) (.leaf 3019586855)) (.branch 25 (.leaf 2944005739) (.leaf 2870824303))) (.branch 28 (.branch 27 (.leaf 2799944691) (.leaf 2731273951)) (.branch 29 (.leaf 2664723751) (.leaf 2600210099)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2537653099) (.branch 32 (.leaf 2476976708) (.leaf 2418108521))) (.branch 35 (.branch 34 (.leaf 2360979563) (.leaf 2305524102)) (.branch 36 (.leaf 2251679464) (.leaf 2199385871)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2148586279) (.leaf 2099226234)) (.branch 40 (.leaf 2051253733) (.leaf 2004619095))) (.branch 43 (.branch 42 (.leaf 1959274836) (.leaf 1915175560)) (.branch 44 (.leaf 1872277847) (.leaf 1830540156))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1789922722) (.branch 47 (.leaf 1750387477) (.leaf 1711897955))) (.branch 50 (.branch 49 (.leaf 1674419219) (.leaf 1637917785)) (.branch 51 (.leaf 1602361545) (.leaf 1567719709)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1533962733) (.leaf 1501062267)) (.branch 55 (.leaf 1468991091) (.leaf 1437723067))) (.branch 58 (.branch 57 (.leaf 1407233083) (.leaf 1377497011)) (.branch 59 (.leaf 1348491658) (.leaf 1320194722))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1292584752) (.branch 62 (.leaf 1265641113) (.leaf 1239343944))) (.branch 65 (.branch 64 (.leaf 1213674124) (.leaf 1188613242)) (.branch 66 (.leaf 1164143563) (.leaf 1140248001)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1116910085) (.leaf 1094113938)) (.branch 70 (.leaf 1071844249) (.leaf 1050086249))) (.branch 73 (.branch 72 (.leaf 1028825688) (.leaf 1008048811)) (.branch 74 (.leaf 987742340) (.leaf 967893453))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 948489765) (.branch 77 (.leaf 929519310) (.leaf 910970522))) (.branch 80 (.branch 79 (.leaf 892832222) (.leaf 875093600)) (.branch 81 (.leaf 857744200) (.leaf 840773909)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 824172936) (.leaf 807931810)) (.branch 85 (.leaf 792041357) (.leaf 776492695))) (.branch 88 (.branch 87 (.leaf 761277221) (.leaf 746386598)) (.branch 89 (.leaf 731812748) (.leaf 717547842)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 703584286) (.branch 92 (.leaf 689914719) (.leaf 676531999))) (.branch 95 (.branch 94 (.leaf 663429199) (.leaf 650599593)) (.branch 96 (.leaf 638036657) (.leaf 625734053)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 613685631) (.leaf 601885413)) (.branch 100 (.leaf 590327596) (.leaf 579006539))) (.branch 103 (.branch 102 (.leaf 567916761) (.leaf 557052932)) (.branch 104 (.leaf 546409873) (.leaf 535982545))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 525766051) (.leaf 515755622)) (.branch 108 (.leaf 505946622) (.leaf 496334538))) (.branch 111 (.branch 110 (.leaf 486914977) (.leaf 477683662)) (.branch 112 (.leaf 468636432) (.leaf 459769230)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 451078108) (.leaf 442559218)) (.branch 116 (.leaf 434208813) (.leaf 426023238))) (.branch 119 (.branch 118 (.leaf 417998936) (.leaf 410132434)) (.branch 120 (.leaf 402420350) (.leaf 394859384)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 965).prefactor = (4617589831488557/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 965).cutoff/(generalMeanRows 965).c)).2 =
    (177832407995967/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 965).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 965).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 965).q*(generalMeanRows 965).c/2-2 = (1453/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable239.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 965).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 965

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 965).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 965).criticalRate j.val*(generalMeanRows 965).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 965).c*(generalMeanRows 965).criticalPoint j.val)).2-
      (generalMeanRows 965).J/2-(generalMeanRows 965).error (generalMeanGrid j.val)+
      (generalMeanRows 965).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 965).c)).2-
      (generalMeanRows 965).J/2-(generalMeanRows 965).error 4 := by
  have he : (generalMeanRows 965).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 965) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 965)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0965

/-! Kernel-checked entropy margins for general spectral rectangle 966. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0966
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5601803338) (.branch 2 (.leaf 5429623636) (.leaf 5264562982))) (.branch 5 (.branch 4 (.leaf 5106233304) (.leaf 4954273533)) (.branch 6 (.leaf 4808347235) (.leaf 4668140496)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4533360032) (.leaf 4403731503)) (.branch 10 (.leaf 4278997990) (.leaf 4158918626))) (.branch 13 (.branch 12 (.leaf 4043267360) (.leaf 3931831838)) (.branch 14 (.leaf 3824412384) (.leaf 3720821081))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3620880923) (.branch 17 (.leaf 3524425052) (.leaf 3431296050))) (.branch 20 (.branch 19 (.leaf 3341345298) (.leaf 3254432381)) (.branch 21 (.leaf 3170424548) (.leaf 3089196210)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3010628477) (.leaf 2934608732)) (.branch 25 (.leaf 2861030240) (.leaf 2789791780))) (.branch 28 (.branch 27 (.leaf 2720797306) (.leaf 2653955638)) (.branch 29 (.leaf 2589180165) (.leaf 2526388580)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2465502622) (.branch 32 (.leaf 2406447845) (.leaf 2349153397))) (.branch 35 (.branch 34 (.leaf 2293551817) (.leaf 2239578842)) (.branch 36 (.leaf 2187173231) (.leaf 2136276595)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2086833244) (.leaf 2038790036)) (.branch 40 (.leaf 1992096245) (.leaf 1946703427))) (.branch 43 (.branch 42 (.leaf 1902565302) (.leaf 1859637639)) (.branch 44 (.leaf 1817878151) (.leaf 1777246391))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1737703661) (.branch 47 (.leaf 1699212920) (.leaf 1661738704))) (.branch 50 (.branch 49 (.leaf 1625247043) (.leaf 1589705386)) (.branch 51 (.leaf 1555082535) (.leaf 1521348576)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1488474817) (.leaf 1456433725)) (.branch 55 (.leaf 1425198877) (.leaf 1394744903))) (.branch 58 (.branch 57 (.leaf 1365047435) (.leaf 1336083061)) (.branch 59 (.leaf 1307829282) (.leaf 1280264467))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1253367814) (.branch 62 (.leaf 1227119311) (.leaf 1201499702))) (.branch 65 (.branch 64 (.leaf 1176490449) (.leaf 1152073705)) (.branch 66 (.leaf 1128232277) (.leaf 1104949604)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1082209721) (.leaf 1059997239)) (.branch 70 (.leaf 1038297319) (.leaf 1017095645))) (.branch 73 (.branch 72 (.leaf 996378405) (.leaf 976132267)) (.branch 74 (.leaf 956344361) (.leaf 937002257))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 918093949) (.branch 77 (.leaf 899607834) (.leaf 881532700))) (.branch 80 (.branch 79 (.leaf 863857706) (.leaf 846572369)) (.branch 81 (.leaf 829666548) (.leaf 813130432)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 796954524) (.leaf 781129633)) (.branch 85 (.leaf 765646857) (.leaf 750497575))) (.branch 88 (.branch 87 (.leaf 735673435) (.leaf 721166344)) (.branch 89 (.leaf 706968457) (.leaf 693072168)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 679470103) (.branch 92 (.leaf 666155107) (.leaf 653120240))) (.branch 95 (.branch 94 (.leaf 640358768) (.leaf 627864152)) (.branch 96 (.leaf 615630048) (.leaf 603650291)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 591918896) (.leaf 580430048)) (.branch 100 (.leaf 569178098) (.leaf 558157552))) (.branch 103 (.branch 102 (.leaf 547363074) (.leaf 536789473)) (.branch 104 (.leaf 526431703) (.leaf 516284853))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 506344149) (.leaf 496604944)) (.branch 108 (.leaf 487062714) (.leaf 477713059))) (.branch 111 (.branch 110 (.leaf 468551691) (.leaf 459574439)) (.branch 112 (.leaf 450777239) (.leaf 442156130)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 433707258) (.leaf 425426863)) (.branch 116 (.leaf 417311284) (.leaf 409356951))) (.branch 119 (.branch 118 (.leaf 401560384) (.leaf 393918191)) (.branch 120 (.leaf 386427064) (.leaf 379083774)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 966).prefactor = (916657400517623/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 966).cutoff/(generalMeanRows 966).c)).2 =
    (91641026612493/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 966).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 966).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 966).q*(generalMeanRows 966).c/2-2 = (59/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable050.value]
    have hcontinuation : (generalMeanRows 966).q*(generalMeanRows 966).cutoff/2-2 = (232/119:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable314.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 966).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 966

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 966).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 966).criticalRate j.val*(generalMeanRows 966).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 966).c*(generalMeanRows 966).criticalPoint j.val)).2-
      (generalMeanRows 966).J/2-(generalMeanRows 966).error (generalMeanGrid j.val)+
      (generalMeanRows 966).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 966).c)).2-
      (generalMeanRows 966).J/2-(generalMeanRows 966).error 4 := by
  have he : (generalMeanRows 966).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 966) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 966)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0966

/-! Kernel-checked entropy margins for general spectral rectangle 967. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0967
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5123849968) (.branch 2 (.leaf 4949387035) (.leaf 4782372085))) (.branch 5 (.branch 4 (.leaf 4622400895) (.leaf 4469097132)) (.branch 6 (.leaf 4322109908) (.leaf 4181111609)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4045795954) (.leaf 3915876248)) (.branch 10 (.leaf 3791083826) (.leaf 3671166638))) (.branch 13 (.branch 12 (.leaf 3555887976) (.leaf 3445025324)) (.branch 14 (.leaf 3338369308) (.leaf 3235722749))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3136899788) (.branch 17 (.leaf 3041725104) (.leaf 2950033177))) (.branch 20 (.branch 19 (.leaf 2861667637) (.leaf 2776480642)) (.branch 21 (.leaf 2694332325) (.leaf 2615090276)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2538629063) (.leaf 2464829797)) (.branch 25 (.leaf 2393579720) (.leaf 2324771832))) (.branch 28 (.branch 27 (.leaf 2258304539) (.leaf 2194081333)) (.branch 29 (.leaf 2132010485) (.leaf 2072004773)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2013981210) (.branch 32 (.leaf 1957860813) (.leaf 1903568368))) (.branch 35 (.branch 34 (.leaf 1851032220) (.leaf 1800184078)) (.branch 36 (.leaf 1750958825) (.leaf 1703294351)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1657131385) (.leaf 1612413344)) (.branch 40 (.leaf 1569086195) (.leaf 1527098314))) (.branch 43 (.branch 42 (.leaf 1486400366) (.leaf 1446945182)) (.branch 44 (.leaf 1408687652) (.leaf 1371584617))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1335594773) (.branch 47 (.leaf 1300678575) (.leaf 1266798154))) (.branch 50 (.branch 49 (.leaf 1233917228) (.leaf 1202001030)) (.branch 51 (.leaf 1171016233) (.leaf 1140930877)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1111714309) (.leaf 1083337115)) (.branch 55 (.leaf 1055771067) (.leaf 1028989063))) (.branch 58 (.branch 57 (.leaf 1002965077) (.leaf 977674106)) (.branch 59 (.leaf 953092129) (.leaf 929196055))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 905963687) (.branch 62 (.leaf 883373676) (.leaf 861405488))) (.branch 65 (.branch 64 (.leaf 840039365) (.leaf 819256291)) (.branch 66 (.leaf 799037959) (.leaf 779366743)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 760225662) (.leaf 741598361)) (.branch 70 (.leaf 723469076) (.leaf 705822614))) (.branch 73 (.branch 72 (.leaf 688644328) (.leaf 671920090)) (.branch 74 (.leaf 655636275) (.leaf 639779738))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 624337792) (.branch 77 (.leaf 609298193) (.leaf 594649118))) (.branch 80 (.branch 79 (.leaf 580379150) (.leaf 566477263)) (.branch 81 (.leaf 552932805) (.leaf 539735481)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 526875343) (.leaf 514342772)) (.branch 85 (.leaf 502128469) (.leaf 490223441))) (.branch 88 (.branch 87 (.leaf 478618988) (.leaf 467306695)) (.branch 89 (.leaf 456278416) (.leaf 445526269)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 435042624) (.branch 92 (.leaf 424820092) (.leaf 414851518))) (.branch 95 (.branch 94 (.leaf 405129973) (.leaf 395648744)) (.branch 96 (.leaf 386401324) (.leaf 377381411)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 368582895) (.leaf 359999852)) (.branch 100 (.leaf 351626539) (.leaf 343457387))) (.branch 103 (.branch 102 (.leaf 335486994) (.leaf 327710121)) (.branch 104 (.leaf 320121683) (.leaf 312716746))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 305490524) (.leaf 298438369)) (.branch 108 (.leaf 291555770) (.leaf 284838345))) (.branch 111 (.branch 110 (.leaf 278281842) (.leaf 271882128)) (.branch 112 (.leaf 265635192) (.leaf 259537133)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 253584166) (.leaf 247772608)) (.branch 116 (.leaf 242098883) (.leaf 236559514))) (.branch 119 (.branch 118 (.leaf 231151120) (.leaf 225870416)) (.branch 120 (.leaf 220714206) (.leaf 215679383)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 967).prefactor = (2367334416394717/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 967).cutoff/(generalMeanRows 967).c)).2 =
    (156609062872339/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 967).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 967).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 967).q*(generalMeanRows 967).c/2-2 = (71/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable027.value]
    have hcontinuation : (generalMeanRows 967).q*(generalMeanRows 967).cutoff/2-2 = (232/119:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable314.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 967).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 967

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 967).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 967).criticalRate j.val*(generalMeanRows 967).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 967).c*(generalMeanRows 967).criticalPoint j.val)).2-
      (generalMeanRows 967).J/2-(generalMeanRows 967).error (generalMeanGrid j.val)+
      (generalMeanRows 967).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 967).c)).2-
      (generalMeanRows 967).J/2-(generalMeanRows 967).error 4 := by
  have he : (generalMeanRows 967).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 967) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 967)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0967

/-! Kernel-checked entropy margins for general spectral rectangle 968. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0968
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5129570649) (.branch 2 (.leaf 4958669669) (.leaf 4795050231))) (.branch 5 (.branch 4 (.leaf 4638313701) (.leaf 4488089132)) (.branch 6 (.leaf 4344030843) (.leaf 4205816260)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4073143981) (.leaf 3945732050)) (.branch 10 (.leaf 3823316399) (.leaf 3705649446))) (.branch 13 (.branch 12 (.leaf 3592498828) (.leaf 3483646250)) (.branch 14 (.leaf 3378886449) (.leaf 3278026239))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3180883653) (.branch 17 (.leaf 3087287150) (.leaf 2997074893))) (.branch 20 (.branch 19 (.leaf 2910094091) (.leaf 2826200385)) (.branch 21 (.leaf 2745257296) (.leaf 2667135707)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2591713387) (.leaf 2518874557)) (.branch 25 (.leaf 2448509483) (.leaf 2380514101))) (.branch 28 (.branch 27 (.leaf 2314789669) (.leaf 2251242446)) (.branch 29 (.leaf 2189783390) (.leaf 2130327884)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2072795470) (.branch 32 (.leaf 2017109615) (.leaf 1963197481))) (.branch 35 (.branch 34 (.leaf 1910989715) (.leaf 1860420255)) (.branch 36 (.leaf 1811426145) (.leaf 1763947363)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1717926662) (.leaf 1673309418)) (.branch 40 (.leaf 1630043487) (.leaf 1588079077))) (.branch 43 (.branch 42 (.leaf 1547368622) (.leaf 1507866662)) (.branch 44 (.leaf 1469529737) (.leaf 1432316283))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1396186534) (.branch 47 (.leaf 1361102431) (.leaf 1327027535))) (.branch 50 (.branch 49 (.leaf 1293926949) (.leaf 1261767237)) (.branch 51 (.leaf 1230516355) (.leaf 1200143581)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1170619452) (.leaf 1141915703)) (.branch 55 (.leaf 1114005210) (.leaf 1086861932))) (.branch 58 (.branch 57 (.leaf 1060460867) (.leaf 1034777996)) (.branch 59 (.leaf 1009790242) (.leaf 985475422))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 961812211) (.branch 62 (.leaf 938780100) (.leaf 916359358))) (.branch 65 (.branch 64 (.leaf 894531000) (.leaf 873276749)) (.branch 66 (.leaf 852579010) (.leaf 832420836)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 812785902) (.leaf 793658474)) (.branch 70 (.leaf 775023390) (.leaf 756866027))) (.branch 73 (.branch 72 (.leaf 739172286) (.leaf 721928566)) (.branch 74 (.leaf 705121741) (.leaf 688739143))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 672768545) (.branch 77 (.leaf 657198138) (.leaf 642016514))) (.branch 80 (.branch 79 (.leaf 627212656) (.leaf 612775913)) (.branch 81 (.leaf 598695995) (.leaf 584962950)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 571567154) (.leaf 558499301)) (.branch 85 (.leaf 545750386) (.leaf 533311695))) (.branch 88 (.branch 87 (.leaf 521174794) (.leaf 509331519)) (.branch 89 (.leaf 497773963) (.leaf 486494470)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 475485621) (.branch 92 (.leaf 464740231) (.leaf 454251334))) (.branch 95 (.branch 94 (.leaf 444012180) (.leaf 434016225)) (.branch 96 (.leaf 424257121) (.leaf 414728715)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 405425035) (.leaf 396340290)) (.branch 100 (.leaf 387468858) (.leaf 378805285))) (.branch 103 (.branch 102 (.leaf 370344275) (.leaf 362080686)) (.branch 104 (.leaf 354009527) (.leaf 346125948))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 338425240) (.leaf 330902826)) (.branch 108 (.leaf 323554262) (.leaf 316375226))) (.branch 111 (.branch 110 (.leaf 309361519) (.leaf 302509059)) (.branch 112 (.leaf 295813875) (.leaf 289272110)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 282880009) (.leaf 276633921)) (.branch 116 (.leaf 270530296) (.leaf 264565678))) (.branch 119 (.branch 118 (.leaf 258736704) (.leaf 253040104)) (.branch 120 (.leaf 247472692) (.leaf 242031370)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 968).prefactor = (4685024656925089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 968).cutoff/(generalMeanRows 968).c)).2 =
    (33101969599/97656250000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 968).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 968).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 968).q*(generalMeanRows 968).c/2-2 = (3433/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable312.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 968).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 968

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 968).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 968).criticalRate j.val*(generalMeanRows 968).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 968).c*(generalMeanRows 968).criticalPoint j.val)).2-
      (generalMeanRows 968).J/2-(generalMeanRows 968).error (generalMeanGrid j.val)+
      (generalMeanRows 968).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 968).c)).2-
      (generalMeanRows 968).J/2-(generalMeanRows 968).error 4 := by
  have he : (generalMeanRows 968).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 968) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 968)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0968

/-! Kernel-checked entropy margins for general spectral rectangle 969. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0969
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5298212217) (.branch 2 (.leaf 5130387949) (.leaf 4969638176))) (.branch 5 (.branch 4 (.leaf 4815571358) (.leaf 4667823422)) (.branch 6 (.leaf 4526055361) (.leaf 4389951078)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4259215474) (.leaf 4133572721)) (.branch 10 (.leaf 4012764716) (.leaf 3896549681))) (.branch 13 (.branch 12 (.leaf 3784700906) (.leaf 3677005603)) (.branch 14 (.leaf 3573263867) (.leaf 3473287734))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3376900319) (.branch 17 (.leaf 3283935027) (.leaf 3194234838))) (.branch 20 (.branch 19 (.leaf 3107651647) (.leaf 3024045655)) (.branch 21 (.leaf 2943284817) (.leaf 2865244326)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2789806145) (.leaf 2716858568)) (.branch 25 (.leaf 2646295818) (.leaf 2578017673))) (.branch 28 (.branch 27 (.leaf 2511929122) (.leaf 2447940045)) (.branch 29 (.leaf 2385964914) (.leaf 2325922518)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2267735704) (.branch 32 (.leaf 2211331139) (.leaf 2156639088))) (.branch 35 (.branch 34 (.leaf 2103593201) (.leaf 2052130328)) (.branch 36 (.leaf 2002190326) (.leaf 1953715898)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1906652433) (.leaf 1860947853)) (.branch 40 (.leaf 1816552479) (.leaf 1773418897))) (.branch 43 (.branch 42 (.leaf 1731501840) (.leaf 1690758066)) (.branch 44 (.leaf 1651146260) (.leaf 1612626923))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1575162282) (.branch 47 (.leaf 1538716203) (.leaf 1503254099))) (.branch 50 (.branch 49 (.leaf 1468742859) (.leaf 1435150766)) (.branch 51 (.leaf 1402447432) (.leaf 1370603731)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1339591732) (.leaf 1309384646)) (.branch 55 (.leaf 1279956767) (.leaf 1251283417))) (.branch 58 (.branch 57 (.leaf 1223340904) (.leaf 1196106466)) (.branch 59 (.leaf 1169558232) (.leaf 1143675179))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1118437093) (.branch 62 (.leaf 1093824529) (.leaf 1069818776))) (.branch 65 (.branch 64 (.leaf 1046401827) (.leaf 1023556342)) (.branch 66 (.leaf 1001265619) (.leaf 979513569)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 958284685) (.leaf 937564015)) (.branch 70 (.leaf 917337142) (.leaf 897590159))) (.branch 73 (.branch 72 (.leaf 878309644) (.leaf 859482643)) (.branch 74 (.leaf 841096648) (.leaf 823139579))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 805599765) (.branch 77 (.leaf 788465928) (.leaf 771727165))) (.branch 80 (.branch 79 (.leaf 755372935) (.leaf 739393043)) (.branch 81 (.leaf 723777624) (.leaf 708517134)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 693602334) (.leaf 679024278)) (.branch 85 (.leaf 664774302) (.leaf 650844014))) (.branch 88 (.branch 87 (.leaf 637225282) (.leaf 623910226)) (.branch 89 (.leaf 610891204) (.leaf 598160808)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 585711854) (.branch 92 (.leaf 573537370) (.leaf 561630593))) (.branch 95 (.branch 94 (.leaf 549984959) (.leaf 538594095)) (.branch 96 (.leaf 527451814) (.leaf 516552106)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 505889136) (.leaf 495457231)) (.branch 100 (.leaf 485250881) (.leaf 475264730))) (.branch 103 (.branch 102 (.leaf 465493570) (.leaf 455932338)) (.branch 104 (.leaf 446576110) (.leaf 437420097))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 428459639) (.leaf 419690203)) (.branch 108 (.leaf 411107376) (.leaf 402706863))) (.branch 111 (.branch 110 (.leaf 394484483) (.leaf 386436165)) (.branch 112 (.leaf 378557945) (.leaf 370845960)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 363296450) (.leaf 355905750)) (.branch 116 (.leaf 348670288) (.leaf 341586584))) (.branch 119 (.branch 118 (.leaf 334651246) (.leaf 327860968)) (.branch 120 (.leaf 321212525) (.leaf 314702773)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 969).prefactor = (925925957871659/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 969).cutoff/(generalMeanRows 969).c)).2 =
    (189286653394403/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 969).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 969).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 969).q*(generalMeanRows 969).c/2-2 = (3169/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable315.value]
    have hcontinuation : (generalMeanRows 969).q*(generalMeanRows 969).cutoff/2-2 = (3496/1683:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable316.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 969).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 969

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 969).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 969).criticalRate j.val*(generalMeanRows 969).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 969).c*(generalMeanRows 969).criticalPoint j.val)).2-
      (generalMeanRows 969).J/2-(generalMeanRows 969).error (generalMeanGrid j.val)+
      (generalMeanRows 969).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 969).c)).2-
      (generalMeanRows 969).J/2-(generalMeanRows 969).error 4 := by
  have he : (generalMeanRows 969).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 969) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 969)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0969

/-! Kernel-checked entropy margins for general spectral rectangle 970. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0970
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5373594234) (.branch 2 (.leaf 5201124074) (.leaf 5035953315))) (.branch 5 (.branch 4 (.leaf 4877678273) (.leaf 4725923554)) (.branch 6 (.leaf 4580339572) (.leaf 4440600343)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4306401507) (.leaf 4177458552)) (.branch 10 (.leaf 4053505226) (.leaf 3934292095))) (.branch 13 (.branch 12 (.leaf 3819585245) (.leaf 3709165105)) (.branch 14 (.leaf 3602825381) (.leaf 3500372079))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3401622621) (.branch 17 (.leaf 3306405037) (.leaf 3214557222))) (.branch 20 (.branch 19 (.leaf 3125926258) (.leaf 3040367793)) (.branch 21 (.leaf 2957745462) (.leaf 2877930368)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2800800590) (.leaf 2726240734)) (.branch 25 (.leaf 2654141523) (.leaf 2584399408))) (.branch 28 (.branch 27 (.leaf 2516916213) (.leaf 2451598807)) (.branch 29 (.leaf 2388358798) (.leaf 2327112246)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2267779397) (.branch 32 (.leaf 2210284444) (.leaf 2154555286))) (.branch 35 (.branch 34 (.leaf 2100523322) (.leaf 2048123249)) (.branch 36 (.leaf 1997292873) (.leaf 1947972936)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1900106952) (.leaf 1853641055)) (.branch 40 (.leaf 1808523853) (.leaf 1764706297))) (.branch 43 (.branch 42 (.leaf 1722141553) (.leaf 1680784881)) (.branch 44 (.leaf 1640593532) (.leaf 1601526634))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1563545100) (.branch 47 (.leaf 1526611534) (.leaf 1490690144))) (.branch 50 (.branch 49 (.leaf 1455746660) (.leaf 1421748258)) (.branch 51 (.leaf 1388663486) (.leaf 1356462196)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1325115481) (.leaf 1294595611)) (.branch 55 (.leaf 1264875979) (.leaf 1235931043))) (.branch 58 (.branch 57 (.leaf 1207736279) (.leaf 1180268128)) (.branch 59 (.leaf 1153503953) (.leaf 1127421996))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1102001334) (.branch 62 (.leaf 1077221843) (.leaf 1053064162))) (.branch 65 (.branch 64 (.leaf 1029509653) (.leaf 1006540373)) (.branch 66 (.leaf 984139043) (.leaf 962289014)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 940974242) (.leaf 920179260)) (.branch 70 (.leaf 899889157) (.leaf 880089544))) (.branch 73 (.branch 72 (.leaf 860766544) (.leaf 841906760)) (.branch 74 (.leaf 823497258) (.leaf 805525550))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 787979571) (.branch 77 (.leaf 770847663) (.leaf 754118560))) (.branch 80 (.branch 79 (.leaf 737781370) (.leaf 721825559)) (.branch 81 (.leaf 706240938) (.leaf 691017649)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 676146151) (.leaf 661617209)) (.branch 85 (.leaf 647421880) (.leaf 633551502))) (.branch 88 (.branch 87 (.leaf 619997686) (.leaf 606752299)) (.branch 89 (.leaf 593807464) (.leaf 581155539)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 568789118) (.branch 92 (.leaf 556701015) (.leaf 544884262))) (.branch 95 (.branch 94 (.leaf 533332095) (.leaf 522037952)) (.branch 96 (.leaf 510995460) (.leaf 500198435)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 489640870) (.leaf 479316928)) (.branch 100 (.leaf 469220942) (.leaf 459347405))) (.branch 103 (.branch 102 (.leaf 449690962) (.leaf 440246410)) (.branch 104 (.leaf 431008692) (.leaf 421972886))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 413134210) (.leaf 404488009)) (.branch 108 (.leaf 396029756) (.leaf 387755044))) (.branch 111 (.branch 110 (.leaf 379659587) (.leaf 371739211)) (.branch 112 (.leaf 363989853) (.leaf 356407557)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 348988470) (.leaf 341728842)) (.branch 116 (.leaf 334625017) (.leaf 327673435))) (.branch 119 (.branch 118 (.leaf 320870626) (.leaf 314213211)) (.branch 120 (.leaf 307697894) (.leaf 301321464)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 970).prefactor = (4768346578662923/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 970).cutoff/(generalMeanRows 970).c)).2 =
    (372058625767613/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 970).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 970).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 970).q*(generalMeanRows 970).c/2-2 = (1621/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable288.value]
    have hcontinuation : (generalMeanRows 970).q*(generalMeanRows 970).cutoff/2-2 = (3496/1683:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable316.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 970).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 970

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 970).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 970).criticalRate j.val*(generalMeanRows 970).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 970).c*(generalMeanRows 970).criticalPoint j.val)).2-
      (generalMeanRows 970).J/2-(generalMeanRows 970).error (generalMeanGrid j.val)+
      (generalMeanRows 970).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 970).c)).2-
      (generalMeanRows 970).J/2-(generalMeanRows 970).error 4 := by
  have he : (generalMeanRows 970).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 970) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 970)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0970

/-! Kernel-checked entropy margins for general spectral rectangle 971. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0971
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5367733527) (.branch 2 (.leaf 5190969996) (.leaf 5021749720))) (.branch 5 (.branch 4 (.leaf 4859656012) (.leaf 4704301321)) (.branch 6 (.leaf 4555324678) (.leaf 4412389425)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4275181176) (.leaf 4143406001)) (.branch 10 (.leaf 4016788779) (.leaf 3895071722))) (.branch 13 (.branch 12 (.leaf 3778013038) (.leaf 3665385720)) (.branch 14 (.leaf 3556976445) (.leaf 3452584574))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3352021240) (.branch 17 (.leaf 3255108514) (.leaf 3161678646))) (.branch 20 (.branch 19 (.leaf 3071573362) (.leaf 2984643223)) (.branch 21 (.leaf 2900747039) (.leaf 2819751323)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2741529789) (.leaf 2665962896)) (.branch 25 (.leaf 2592937411) (.leaf 2522346025))) (.branch 28 (.branch 27 (.leaf 2454086976) (.leaf 2388063717)) (.branch 29 (.leaf 2324184596) (.leaf 2262362563)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2202514900) (.branch 32 (.leaf 2144562965) (.leaf 2088431954))) (.branch 35 (.branch 34 (.leaf 2034050681) (.leaf 1981351374)) (.branch 36 (.leaf 1930269479) (.leaf 1880743481)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1832714735) (.leaf 1786127310)) (.branch 40 (.leaf 1740927839) (.leaf 1697065382))) (.branch 43 (.branch 42 (.leaf 1654491293) (.leaf 1613159101)) (.branch 44 (.leaf 1573024397) (.leaf 1534044718))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1496179455) (.branch 47 (.leaf 1459389754) (.leaf 1423638424))) (.branch 50 (.branch 49 (.leaf 1388889855) (.leaf 1355109939)) (.branch 51 (.leaf 1322265993) (.leaf 1290326690)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1259261991) (.leaf 1229043082)) (.branch 55 (.leaf 1199642315) (.leaf 1171033153))) (.branch 58 (.branch 57 (.leaf 1143190114) (.leaf 1116088723)) (.branch 59 (.leaf 1089705464) (.leaf 1064017735))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1039003806) (.branch 62 (.leaf 1014642776) (.leaf 990914539))) (.branch 65 (.branch 64 (.leaf 967799748) (.leaf 945279774)) (.branch 66 (.leaf 923336682) (.leaf 901953196)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 881112668) (.leaf 860799056)) (.branch 70 (.leaf 840996892) (.leaf 821691260))) (.branch 73 (.branch 72 (.leaf 802867771) (.leaf 784512543)) (.branch 74 (.leaf 766612176) (.leaf 749153733))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 732124721) (.branch 77 (.leaf 715513074) (.leaf 699307131))) (.branch 80 (.branch 79 (.leaf 683495626) (.leaf 668067665)) (.branch 81 (.leaf 653012715) (.leaf 638320589)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 623981432) (.leaf 609985707)) (.branch 85 (.leaf 596324185) (.leaf 582987929))) (.branch 88 (.branch 87 (.leaf 569968287) (.leaf 557256878)) (.branch 89 (.leaf 544845583) (.leaf 532726535)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 520892109) (.branch 92 (.leaf 509334914) (.leaf 498047782))) (.branch 95 (.branch 94 (.leaf 487023764) (.leaf 476256118)) (.branch 96 (.leaf 465738302) (.leaf 455463970)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 445426960) (.leaf 435621294)) (.branch 100 (.leaf 426041164) (.leaf 416680932))) (.branch 103 (.branch 102 (.leaf 407535121) (.leaf 398598411)) (.branch 104 (.leaf 389865632) (.leaf 381331761))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 372991916) (.leaf 364841350)) (.branch 108 (.leaf 356875447) (.leaf 349089722))) (.branch 111 (.branch 110 (.leaf 341479810) (.leaf 334041465)) (.branch 112 (.leaf 326770558) (.leaf 319663071)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 312715093) (.leaf 305922819)) (.branch 116 (.leaf 299282544) (.leaf 292790662))) (.branch 119 (.branch 118 (.leaf 286443663) (.leaf 280238126)) (.branch 120 (.leaf 274170722) (.leaf 268238208)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 971).prefactor = (491121971491331/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 971).cutoff/(generalMeanRows 971).c)).2 =
    (44894402616463/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 971).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 971).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 971).q*(generalMeanRows 971).c/2-2 = (847/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable287.value]
    have hcontinuation : (generalMeanRows 971).q*(generalMeanRows 971).cutoff/2-2 = (3496/1683:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable316.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 971).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 971

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 971).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 971).criticalRate j.val*(generalMeanRows 971).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 971).c*(generalMeanRows 971).criticalPoint j.val)).2-
      (generalMeanRows 971).J/2-(generalMeanRows 971).error (generalMeanGrid j.val)+
      (generalMeanRows 971).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 971).c)).2-
      (generalMeanRows 971).J/2-(generalMeanRows 971).error 4 := by
  have he : (generalMeanRows 971).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 971) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 971)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0971

/-! Kernel-checked entropy margins for general spectral rectangle 972. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0972
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5445067133) (.branch 2 (.leaf 5263499409) (.leaf 5089713099))) (.branch 5 (.branch 4 (.leaf 4923278538) (.leaf 4763796066)) (.branch 6 (.leaf 4610893410) (.leaf 4464223333)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4323461549) (.leaf 4188304841)) (.branch 10 (.leaf 4058469371) (.leaf 3933689164))) (.branch 13 (.branch 12 (.leaf 3813714723) (.leaf 3698311788)) (.branch 14 (.leaf 3587260201) (.leaf 3480352877))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3377394863) (.branch 17 (.leaf 3278202482) (.leaf 3182602549))) (.branch 20 (.branch 19 (.leaf 3090431647) (.leaf 3001535471)) (.branch 21 (.leaf 2915768219) (.leaf 2832992032)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2753076480) (.leaf 2675898084)) (.branch 25 (.leaf 2601339879) (.leaf 2529291003))) (.branch 28 (.branch 27 (.leaf 2459646324) (.leaf 2392306083)) (.branch 29 (.leaf 2327175578) (.leaf 2264164854)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2203188427) (.branch 32 (.leaf 2144165018) (.leaf 2087017312))) (.branch 35 (.branch 34 (.leaf 2031671731) (.leaf 1978058216)) (.branch 36 (.leaf 1926110037) (.leaf 1875763599)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1826958273) (.leaf 1779636232)) (.branch 40 (.leaf 1733742299) (.leaf 1689223802))) (.branch 43 (.branch 42 (.leaf 1646030443) (.leaf 1604114171)) (.branch 44 (.leaf 1563429061) (.leaf 1523931208))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1485578617) (.branch 47 (.leaf 1448331109) (.leaf 1412150226))) (.branch 50 (.branch 49 (.leaf 1376999145) (.leaf 1342842595)) (.branch 51 (.leaf 1309646779) (.leaf 1277379304)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1246009108) (.leaf 1215506399)) (.branch 55 (.leaf 1185842589) (.leaf 1156990240))) (.branch 58 (.branch 57 (.leaf 1128923009) (.leaf 1101615591)) (.branch 59 (.leaf 1075043678) (.leaf 1049183906))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1024013813) (.branch 62 (.leaf 999511799) (.leaf 975657085))) (.branch 65 (.branch 64 (.leaf 952429677) (.leaf 929810329)) (.branch 66 (.leaf 907780509) (.leaf 886322369)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 865418717) (.leaf 845052981)) (.branch 70 (.leaf 825209189) (.leaf 805871940))) (.branch 73 (.branch 72 (.leaf 787026379) (.leaf 768658175)) (.branch 74 (.leaf 750753500) (.leaf 733299003))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 716281796) (.branch 77 (.leaf 699689431) (.leaf 683509881))) (.branch 80 (.branch 79 (.leaf 667731529) (.leaf 652343144)) (.branch 81 (.leaf 637333868) (.leaf 622693203)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 608410994) (.leaf 594477419)) (.branch 85 (.leaf 580882971) (.leaf 567618449))) (.branch 88 (.branch 87 (.leaf 554674945) (.leaf 542043835)) (.branch 89 (.leaf 529716766) (.leaf 517685643)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 505942626) (.branch 92 (.leaf 494480117) (.leaf 483290747))) (.branch 95 (.branch 94 (.leaf 472367377) (.leaf 461703079)) (.branch 96 (.leaf 451291136) (.leaf 441125032)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 431198445) (.leaf 421505237)) (.branch 100 (.leaf 412039453) (.leaf 402795311))) (.branch 103 (.branch 102 (.leaf 393767197) (.leaf 384949658)) (.branch 104 (.leaf 376337399) (.leaf 367925275))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 359708287) (.leaf 351681578)) (.branch 108 (.leaf 343840426) (.leaf 336180242))) (.branch 111 (.branch 110 (.leaf 328696564) (.leaf 321385054)) (.branch 112 (.leaf 314241492) (.leaf 307261774)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300441909) (.leaf 293778012)) (.branch 116 (.leaf 287266305) (.leaf 280903109))) (.branch 119 (.branch 118 (.leaf 274684846) (.leaf 268608030)) (.branch 120 (.leaf 262669271) (.leaf 256865266)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 972).prefactor = (632296716750941/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 972).cutoff/(generalMeanRows 972).c)).2 =
    (352765422832933/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 972).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 972).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 972).q*(generalMeanRows 972).cutoff/2-2 = (3496/1683:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable316.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 972).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 972

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 972).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 972).criticalRate j.val*(generalMeanRows 972).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 972).c*(generalMeanRows 972).criticalPoint j.val)).2-
      (generalMeanRows 972).J/2-(generalMeanRows 972).error (generalMeanGrid j.val)+
      (generalMeanRows 972).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 972).c)).2-
      (generalMeanRows 972).J/2-(generalMeanRows 972).error 4 := by
  have he : (generalMeanRows 972).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 972) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 972)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0972

/-! Kernel-checked entropy margins for general spectral rectangle 973. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0973
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5694217448) (.branch 2 (.leaf 5506702554) (.leaf 5327189721))) (.branch 5 (.branch 4 (.leaf 5155236919) (.leaf 4990433025)) (.branch 6 (.leaf 4832395113) (.leaf 4680766048)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4535212324) (.leaf 4395422132)) (.branch 10 (.leaf 4261103617) (.leaf 4131983312))) (.branch 13 (.branch 12 (.leaf 4007804719) (.leaf 3888327022)) (.branch 14 (.leaf 3773323924) (.leaf 3662582582))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3555902642) (.branch 17 (.leaf 3453095353) (.leaf 3353982760))) (.branch 20 (.branch 19 (.leaf 3258396964) (.leaf 3166179437)) (.branch 21 (.leaf 3077180400) (.leaf 2991258247)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2908279012) (.leaf 2828115881)) (.branch 25 (.leaf 2750648737) (.leaf 2675763741))) (.branch 28 (.branch 27 (.leaf 2603352944) (.leaf 2533313924)) (.branch 29 (.leaf 2465549456) (.leaf 2399967195)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2336479393) (.branch 32 (.leaf 2275002623) (.leaf 2215457531))) (.branch 35 (.branch 34 (.leaf 2157768604) (.leaf 2101863945)) (.branch 36 (.leaf 2047675074) (.leaf 1995136735)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1944186716) (.leaf 1894765685)) (.branch 40 (.leaf 1846817027) (.leaf 1800286705))) (.branch 43 (.branch 42 (.leaf 1755123114) (.leaf 1711276958)) (.branch 44 (.leaf 1668701123) (.leaf 1627350567))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1587182210) (.branch 47 (.leaf 1548154833) (.leaf 1510228984))) (.branch 50 (.branch 49 (.leaf 1473366888) (.leaf 1437532362)) (.branch 51 (.leaf 1402690735) (.leaf 1368808774)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1335854614) (.leaf 1303797688)) (.branch 55 (.leaf 1272608666) (.leaf 1242259397))) (.branch 58 (.branch 57 (.leaf 1212722849) (.leaf 1183973059)) (.branch 59 (.leaf 1155985080) (.leaf 1128734935))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1102199572) (.branch 62 (.leaf 1076356821) (.leaf 1051185352))) (.branch 65 (.branch 64 (.leaf 1026664640) (.leaf 1002774924)) (.branch 66 (.leaf 979497179) (.leaf 956813075)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 934704956) (.leaf 913155800)) (.branch 70 (.leaf 892149201) (.leaf 871669334))) (.branch 73 (.branch 72 (.leaf 851700937) (.leaf 832229281)) (.branch 74 (.leaf 813240152) (.leaf 794719826))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 776655052) (.branch 77 (.leaf 759033027) (.leaf 741841384))) (.branch 80 (.branch 79 (.leaf 725068169) (.leaf 708701826)) (.branch 81 (.leaf 692731182) (.leaf 677145431)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 661934117) (.leaf 647087125)) (.branch 85 (.leaf 632594662) (.leaf 618447250))) (.branch 88 (.branch 87 (.leaf 604635709) (.leaf 591151148)) (.branch 89 (.leaf 577984956) (.leaf 565128786)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 552574550) (.branch 92 (.leaf 540314406) (.leaf 528340753))) (.branch 95 (.branch 94 (.leaf 516646216) (.leaf 505223645)) (.branch 96 (.leaf 494066099) (.leaf 483166847)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 472519352) (.leaf 462117272)) (.branch 100 (.leaf 451954445) (.leaf 442024892))) (.branch 103 (.branch 102 (.leaf 432322802) (.leaf 422842530)) (.branch 104 (.leaf 413578594) (.leaf 404525664))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 395678561) (.leaf 387032249)) (.branch 108 (.leaf 378581833) (.leaf 370322554))) (.branch 111 (.branch 110 (.leaf 362249780) (.leaf 354359010)) (.branch 112 (.leaf 346645862) (.leaf 339106073)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 331735495) (.leaf 324530091)) (.branch 116 (.leaf 317485933) (.leaf 310599192))) (.branch 119 (.branch 118 (.leaf 303866146) (.leaf 297283168)) (.branch 120 (.leaf 290846724) (.leaf 284553374)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 973).prefactor = (5209936903291017/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 973).cutoff/(generalMeanRows 973).c)).2 =
    (44894402616463/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 973).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 973).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 973).q*(generalMeanRows 973).c/2-2 = (847/1000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable287.value]
    have hcontinuation : (generalMeanRows 973).q*(generalMeanRows 973).cutoff/2-2 = (3496/1683:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable316.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 973).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 973

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 973).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 973).criticalRate j.val*(generalMeanRows 973).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 973).c*(generalMeanRows 973).criticalPoint j.val)).2-
      (generalMeanRows 973).J/2-(generalMeanRows 973).error (generalMeanGrid j.val)+
      (generalMeanRows 973).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 973).c)).2-
      (generalMeanRows 973).J/2-(generalMeanRows 973).error 4 := by
  have he : (generalMeanRows 973).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 973) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 973)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0973

/-! Kernel-checked entropy margins for general spectral rectangle 974. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0974
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6050988458) (.branch 2 (.leaf 5859319520) (.leaf 5675730230))) (.branch 5 (.branch 4 (.leaf 5499773416) (.leaf 5331033280)) (.branch 6 (.leaf 5169122645) (.leaf 5013680505)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4864369833) (.leaf 4720875609)) (.branch 10 (.leaf 4582903059) (.leaf 4450176055))) (.branch 13 (.branch 12 (.leaf 4322435675) (.leaf 4199438896)) (.branch 14 (.leaf 4080957412) (.leaf 3966776552))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3856694299) (.branch 17 (.leaf 3750520389) (.leaf 3648075492))) (.branch 20 (.branch 19 (.leaf 3549190459) (.leaf 3453705629)) (.branch 21 (.leaf 3361470195) (.leaf 3272341619)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3186185093) (.leaf 3102873038)) (.branch 25 (.leaf 3022284649) (.leaf 2944305464))) (.branch 28 (.branch 27 (.leaf 2868826974) (.leaf 2795746254)) (.branch 29 (.leaf 2724965624) (.leaf 2656392333)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2589938268) (.branch 32 (.leaf 2525519676) (.leaf 2463056913))) (.branch 35 (.branch 34 (.leaf 2402474205) (.leaf 2343699425)) (.branch 36 (.leaf 2286663889) (.leaf 2231302157)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2177551859) (.leaf 2125353519)) (.branch 40 (.leaf 2074650397) (.leaf 2025388346))) (.branch 43 (.branch 42 (.leaf 1977515663) (.leaf 1930982967)) (.branch 44 (.leaf 1885743068) (.leaf 1841750858))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1798963197) (.branch 47 (.leaf 1757338816) (.leaf 1716838215))) (.branch 50 (.branch 49 (.leaf 1677423576) (.leaf 1639058679)) (.branch 51 (.leaf 1601708818) (.leaf 1565340725)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1529922505) (.leaf 1495423561)) (.branch 55 (.leaf 1461814534) (.leaf 1429067241))) (.branch 58 (.branch 57 (.leaf 1397154622) (.leaf 1366050683)) (.branch 59 (.leaf 1335730445) (.leaf 1306169898))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1277345955) (.branch 62 (.leaf 1249236408) (.leaf 1221819890))) (.branch 65 (.branch 64 (.leaf 1195075833) (.leaf 1168984434)) (.branch 66 (.leaf 1143526619) (.leaf 1118684013)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1094438903) (.leaf 1070774216)) (.branch 70 (.leaf 1047673486) (.leaf 1025120828))) (.branch 73 (.branch 72 (.leaf 1003100914) (.leaf 981598951)) (.branch 74 (.leaf 960600652) (.leaf 940092221))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 920060330) (.branch 77 (.leaf 900492097) (.leaf 881375071))) (.branch 80 (.branch 79 (.leaf 862697213) (.leaf 844446878)) (.branch 81 (.leaf 826612803) (.leaf 809184085)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 792150172) (.leaf 775500848)) (.branch 85 (.leaf 759226219) (.leaf 743316699))) (.branch 88 (.branch 87 (.leaf 727763002) (.leaf 712556126)) (.branch 89 (.leaf 697687346) (.leaf 683148201)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 668930485) (.branch 92 (.leaf 655026236) (.leaf 641427730))) (.branch 95 (.branch 94 (.leaf 628127470) (.leaf 615118179)) (.branch 96 (.leaf 602392789) (.leaf 589944439)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 577766461) (.leaf 565852379)) (.branch 100 (.leaf 554195899) (.leaf 542790903))) (.branch 103 (.branch 102 (.leaf 531631445) (.leaf 520711742)) (.branch 104 (.leaf 510026170) (.leaf 499569260))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 489335690) (.leaf 479320282)) (.branch 108 (.leaf 469517996) (.leaf 459923929))) (.branch 111 (.branch 110 (.leaf 450533303) (.leaf 441341471)) (.branch 112 (.leaf 432343904) (.leaf 423536191)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 414914038) (.leaf 406473258)) (.branch 116 (.leaf 398209773) (.leaf 390119609))) (.branch 119 (.branch 118 (.leaf 382198890) (.leaf 374443841)) (.branch 120 (.leaf 366850779) (.leaf 359416114)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 974).prefactor = (5287413050563001/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 974).cutoff/(generalMeanRows 974).c)).2 =
    (189286653394403/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 974).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 974).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 974).q*(generalMeanRows 974).c/2-2 = (3169/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable315.value]
    have hcontinuation : (generalMeanRows 974).q*(generalMeanRows 974).cutoff/2-2 = (3496/1683:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable316.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 974).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 974

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 974).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 974).criticalRate j.val*(generalMeanRows 974).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 974).c*(generalMeanRows 974).criticalPoint j.val)).2-
      (generalMeanRows 974).J/2-(generalMeanRows 974).error (generalMeanGrid j.val)+
      (generalMeanRows 974).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 974).c)).2-
      (generalMeanRows 974).J/2-(generalMeanRows 974).error 4 := by
  have he : (generalMeanRows 974).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 974) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 974)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0974

/-! Kernel-checked entropy margins for general spectral rectangle 975. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0975
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7523302539) (.branch 2 (.leaf 7314444272) (.leaf 7113565305))) (.branch 5 (.branch 4 (.leaf 6920254478) (.leaf 6734128845)) (.branch 6 (.leaf 6554831125) (.leaf 6382027455)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6215405382) (.leaf 6054672082)) (.branch 10 (.leaf 5899552756) (.leaf 5749789200))) (.branch 13 (.branch 12 (.leaf 5605138515) (.leaf 5465371942)) (.branch 14 (.leaf 5330273810) (.leaf 5199640583))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5073279994) (.branch 17 (.leaf 4951010257) (.leaf 4832659343))) (.branch 20 (.branch 19 (.leaf 4718064327) (.leaf 4607070783)) (.branch 21 (.leaf 4499532232) (.leaf 4395309633)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4294270914) (.leaf 4196290545)) (.branch 25 (.leaf 4101249134) (.leaf 4009033062))) (.branch 28 (.branch 27 (.leaf 3919534140) (.leaf 3832649292)) (.branch 29 (.leaf 3748280263) (.leaf 3666333344)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3586719116) (.branch 32 (.leaf 3509352218) (.leaf 3434151117))) (.branch 35 (.branch 34 (.leaf 3361037911) (.leaf 3289938128)) (.branch 36 (.leaf 3220780549) (.leaf 3153497037)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3088022378) (.leaf 3024294135)) (.branch 40 (.leaf 2962252502) (.leaf 2901840177))) (.branch 43 (.branch 42 (.leaf 2843002236) (.leaf 2785686017)) (.branch 44 (.leaf 2729841010) (.leaf 2675418755))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2622372740) (.branch 47 (.leaf 2570658312) (.leaf 2520232590))) (.branch 50 (.branch 49 (.leaf 2471054382) (.leaf 2423084105)) (.branch 51 (.leaf 2376283714) (.leaf 2330616631)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2286047678) (.leaf 2242543018)) (.branch 55 (.leaf 2200070088) (.leaf 2158597552))) (.branch 58 (.branch 57 (.leaf 2118095239) (.leaf 2078534098)) (.branch 59 (.leaf 2039886147) (.leaf 2002124426))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1965222957) (.branch 62 (.leaf 1929156699) (.leaf 1893901509))) (.branch 65 (.branch 64 (.leaf 1859434107) (.leaf 1825732036)) (.branch 66 (.leaf 1792773631) (.leaf 1760537987)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1729004923) (.leaf 1698154959)) (.branch 70 (.leaf 1667969283) (.leaf 1638429727))) (.branch 73 (.branch 72 (.leaf 1609518737) (.leaf 1581219356)) (.branch 74 (.leaf 1553515191) (.leaf 1526390400))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1499829664) (.branch 77 (.leaf 1473818167) (.leaf 1448341583))) (.branch 80 (.branch 79 (.leaf 1423386048) (.leaf 1398938149)) (.branch 81 (.leaf 1374984903) (.leaf 1351513743)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1328512502) (.leaf 1305969397)) (.branch 85 (.leaf 1283873013) (.leaf 1262212295))) (.branch 88 (.branch 87 (.leaf 1240976528) (.leaf 1220155329)) (.branch 89 (.leaf 1199738633) (.leaf 1179716681)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1160080012) (.branch 92 (.leaf 1140819446) (.leaf 1121926081))) (.branch 95 (.branch 94 (.leaf 1103391279) (.leaf 1085206656)) (.branch 96 (.leaf 1067364077) (.leaf 1049855642)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1032673682) (.leaf 1015810749)) (.branch 100 (.leaf 999259608) (.leaf 983013232))) (.branch 103 (.branch 102 (.leaf 967064790) (.leaf 951407647)) (.branch 104 (.leaf 936035351) (.leaf 920941631))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 906120390) (.leaf 891565696)) (.branch 108 (.leaf 877271782) (.leaf 863233035))) (.branch 111 (.branch 110 (.leaf 849443996) (.leaf 835899351)) (.branch 112 (.leaf 822593927) (.leaf 809522689)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 796680736) (.leaf 784063292)) (.branch 116 (.leaf 771665709) (.leaf 759483456))) (.branch 119 (.branch 118 (.leaf 747512120) (.leaf 735747400)) (.branch 120 (.leaf 724185107) (.leaf 712821153)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 975).prefactor = (4943903832718927/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 975).cutoff/(generalMeanRows 975).c)).2 =
    (78037294638943/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 975).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 975).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 975).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 975

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 975).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 975).criticalRate j.val*(generalMeanRows 975).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 975).c*(generalMeanRows 975).criticalPoint j.val)).2-
      (generalMeanRows 975).J/2-(generalMeanRows 975).error (generalMeanGrid j.val)+
      (generalMeanRows 975).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 975).c)).2-
      (generalMeanRows 975).J/2-(generalMeanRows 975).error 4 := by
  have he : (generalMeanRows 975).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 975) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 975)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0975

/-! Kernel-checked entropy margins for general spectral rectangle 976. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0976
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7086312500) (.branch 2 (.leaf 6879715828) (.leaf 6681137312))) (.branch 5 (.branch 4 (.leaf 6490163002) (.leaf 6306407278)) (.branch 6 (.leaf 6129510309) (.leaf 5959135799)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5794968985) (.leaf 5636714844)) (.branch 10 (.leaf 5484096494) (.leaf 5336853758))) (.branch 13 (.branch 12 (.leaf 5194741867) (.leaf 5057530292)) (.branch 14 (.leaf 4925001692) (.leaf 4796950953))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4673184314) (.branch 17 (.leaf 4553518583) (.leaf 4437780403))) (.branch 20 (.branch 19 (.leaf 4325805596) (.leaf 4217438556)) (.branch 21 (.leaf 4112531691) (.leaf 4010944911)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3912545157) (.leaf 3817205967)) (.branch 25 (.leaf 3724807073) (.leaf 3635234030))) (.branch 28 (.branch 27 (.leaf 3548377870) (.leaf 3464134787)) (.branch 29 (.leaf 3382405836) (.leaf 3303096659)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3226117225) (.branch 32 (.leaf 3151381596) (.leaf 3078807701))) (.branch 35 (.branch 34 (.leaf 3008317124) (.leaf 2939834913)) (.branch 36 (.leaf 2873289398) (.leaf 2808612014)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2745737146) (.leaf 2684601977)) (.branch 40 (.leaf 2625146346) (.leaf 2567312614))) (.branch 43 (.branch 42 (.leaf 2511045540) (.leaf 2456292165)) (.branch 44 (.leaf 2403001695) (.leaf 2351125405))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2300616532) (.branch 47 (.leaf 2251430188) (.leaf 2203523269))) (.branch 50 (.branch 49 (.leaf 2156854369) (.leaf 2111383709)) (.branch 51 (.leaf 2067073056) (.leaf 2023885654)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1981786158) (.leaf 1940740571)) (.branch 55 (.leaf 1900716182) (.leaf 1861681512))) (.branch 58 (.branch 57 (.leaf 1823606258) (.leaf 1786461241)) (.branch 59 (.leaf 1750218359) (.leaf 1714850540))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1680331699) (.branch 62 (.leaf 1646636692) (.leaf 1613741282))) (.branch 65 (.branch 64 (.leaf 1581622097) (.leaf 1550256595)) (.branch 66 (.leaf 1519623030) (.leaf 1489700419)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1460468511) (.leaf 1431907756)) (.branch 70 (.leaf 1403999277) (.leaf 1376724844))) (.branch 73 (.branch 72 (.leaf 1350066849) (.leaf 1324008276)) (.branch 74 (.leaf 1298532685) (.leaf 1273624183))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1249267406) (.branch 77 (.leaf 1225447498) (.leaf 1202150090))) (.branch 80 (.branch 79 (.leaf 1179361283) (.leaf 1157067628)) (.branch 81 (.leaf 1135256110) (.leaf 1113914133)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1093029500) (.leaf 1072590402)) (.branch 85 (.leaf 1052585404) (.leaf 1033003426))) (.branch 88 (.branch 87 (.leaf 1013833736) (.leaf 995065931)) (.branch 89 (.leaf 976689931) (.leaf 958695964)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 941074555) (.branch 92 (.leaf 923816516) (.leaf 906912934))) (.branch 95 (.branch 94 (.leaf 890355165) (.leaf 874134820)) (.branch 96 (.leaf 858243758) (.leaf 842674080)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 827418113) (.leaf 812468412)) (.branch 100 (.leaf 797817744) (.leaf 783459084))) (.branch 103 (.branch 102 (.leaf 769385608) (.leaf 755590687)) (.branch 104 (.leaf 742067877) (.leaf 728810916))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 715813717) (.leaf 703070361)) (.branch 108 (.leaf 690575094) (.leaf 678322318))) (.branch 111 (.branch 110 (.leaf 666306589) (.leaf 654522610)) (.branch 112 (.leaf 642965227) (.leaf 631629425)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 620510322) (.leaf 609603166)) (.branch 116 (.leaf 598903330) (.leaf 588406307))) (.branch 119 (.branch 118 (.leaf 578107712) (.leaf 568003269)) (.branch 120 (.leaf 558088814) (.leaf 548360291)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 976).prefactor = (1240786087766947/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 976).cutoff/(generalMeanRows 976).c)).2 =
    (7433282847129/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 976).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 976).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 976).q*(generalMeanRows 976).c/2-2 = (2611/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable317.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 976).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 976

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 976).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 976).criticalRate j.val*(generalMeanRows 976).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 976).c*(generalMeanRows 976).criticalPoint j.val)).2-
      (generalMeanRows 976).J/2-(generalMeanRows 976).error (generalMeanGrid j.val)+
      (generalMeanRows 976).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 976).c)).2-
      (generalMeanRows 976).J/2-(generalMeanRows 976).error 4 := by
  have he : (generalMeanRows 976).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 976) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 976)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0976

/-! Kernel-checked entropy margins for general spectral rectangle 977. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0977
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6714757997) (.branch 2 (.leaf 6511285374) (.leaf 6315834667))) (.branch 5 (.branch 4 (.leaf 6127990175) (.leaf 5947364595)) (.branch 6 (.leaf 5773596491) (.leaf 5606348041)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5445303033) (.leaf 5290165079)) (.branch 10 (.leaf 5140656010) (.leaf 4996514441))) (.branch 13 (.branch 12 (.leaf 4857494469) (.leaf 4723364513)) (.branch 14 (.leaf 4593906244) (.leaf 4468913633))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4348192072) (.branch 17 (.leaf 4231557579) (.leaf 4118836074))) (.branch 20 (.branch 19 (.leaf 4009862712) (.leaf 3904481271)) (.branch 21 (.leaf 3802543596) (.leaf 3703909084)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3608444208) (.leaf 3516022081)) (.branch 25 (.leaf 3426522050) (.leaf 3339829323))) (.branch 28 (.branch 27 (.leaf 3255834624) (.leaf 3174433868)) (.branch 29 (.leaf 3095527865) (.leaf 3019022039)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2944826172) (.branch 32 (.leaf 2872854163) (.leaf 2803023799))) (.branch 35 (.branch 34 (.leaf 2735256549) (.leaf 2669477363)) (.branch 36 (.leaf 2605614493) (.leaf 2543599315)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2483366170) (.leaf 2424852213)) (.branch 40 (.leaf 2367997268) (.leaf 2312743696))) (.branch 43 (.branch 42 (.leaf 2259036266) (.leaf 2206822041)) (.branch 44 (.leaf 2156050261) (.leaf 2106672240))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2058641266) (.branch 47 (.leaf 2011912509) (.leaf 1966442928))) (.branch 50 (.branch 49 (.leaf 1922191191) (.leaf 1879117595)) (.branch 51 (.leaf 1837183990) (.leaf 1796353706)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1756591492) (.leaf 1717863446)) (.branch 55 (.leaf 1680136957) (.leaf 1643380647))) (.branch 58 (.branch 57 (.leaf 1607564319) (.leaf 1572658903)) (.branch 59 (.leaf 1538636405) (.leaf 1505469865))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1473133312) (.branch 62 (.leaf 1441601717) (.leaf 1410850958))) (.branch 65 (.branch 64 (.leaf 1380857782) (.leaf 1351599762)) (.branch 66 (.leaf 1323055273) (.leaf 1295203450)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1268024160) (.leaf 1241497973)) (.branch 70 (.leaf 1215606133) (.leaf 1190330528))) (.branch 73 (.branch 72 (.leaf 1165653669) (.leaf 1141558662)) (.branch 74 (.leaf 1118029183) (.leaf 1095049459))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1072604245) (.branch 77 (.leaf 1050678803) (.leaf 1029258879))) (.branch 80 (.branch 79 (.leaf 1008330694) (.leaf 987880913)) (.branch 81 (.leaf 967896639) (.leaf 948365389)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 929275082) (.leaf 910614024)) (.branch 85 (.leaf 892370891) (.leaf 874534717))) (.branch 88 (.branch 87 (.leaf 857094880) (.leaf 840041092)) (.branch 89 (.leaf 823363380) (.leaf 807052085)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 791097838) (.branch 92 (.leaf 775491562) (.leaf 760224451))) (.branch 95 (.branch 94 (.leaf 745287968) (.leaf 730673832)) (.branch 96 (.leaf 716374006) (.leaf 702380697)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 688686337) (.leaf 675283585)) (.branch 100 (.leaf 662165310) (.leaf 649324591))) (.branch 103 (.branch 102 (.leaf 636754707) (.leaf 624449129)) (.branch 104 (.leaf 612401514) (.leaf 600605702))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 589055704) (.leaf 577745702)) (.branch 108 (.leaf 566670040) (.leaf 555823219))) (.branch 111 (.branch 110 (.leaf 545199891) (.leaf 534794858)) (.branch 112 (.leaf 524603063) (.leaf 514619586)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 504839641) (.leaf 495258573)) (.branch 116 (.leaf 485871848) (.leaf 476675056))) (.branch 119 (.branch 118 (.leaf 467663903) (.leaf 458834209)) (.branch 120 (.leaf 450181903) (.leaf 441703022)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 977).prefactor = (4968678662322879/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 977).cutoff/(generalMeanRows 977).c)).2 =
    (288249609356927/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 977).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 977).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 977).q*(generalMeanRows 977).c/2-2 = (71/100:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable291.value]
    have hcontinuation : (generalMeanRows 977).q*(generalMeanRows 977).cutoff/2-2 = (21/13:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable056.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 977).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 977

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 977).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 977).criticalRate j.val*(generalMeanRows 977).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 977).c*(generalMeanRows 977).criticalPoint j.val)).2-
      (generalMeanRows 977).J/2-(generalMeanRows 977).error (generalMeanGrid j.val)+
      (generalMeanRows 977).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 977).c)).2-
      (generalMeanRows 977).J/2-(generalMeanRows 977).error 4 := by
  have he : (generalMeanRows 977).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 977) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 977)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0977

/-! Kernel-checked entropy margins for general spectral rectangle 978. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0978
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6400872090) (.branch 2 (.leaf 6201076605) (.leaf 6009273969))) (.branch 5 (.branch 4 (.leaf 5825047857) (.leaf 5648010366)) (.branch 6 (.leaf 5477799485) (.leaf 5314076854)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5156525762) (.leaf 5004849367)) (.branch 10 (.leaf 4858769090) (.leaf 4718023182))) (.branch 13 (.branch 12 (.leaf 4582365424) (.leaf 4451563959)) (.branch 14 (.leaf 4325400234) (.leaf 4203668034))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4086172608) (.branch 17 (.leaf 3972729872) (.leaf 3863165682))) (.branch 20 (.branch 19 (.leaf 3757315163) (.leaf 3655022100)) (.branch 21 (.leaf 3556138375) (.leaf 3460523453)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3368043903) (.leaf 3278572959)) (.branch 25 (.leaf 3191990115) (.leaf 3108180748))) (.branch 28 (.branch 27 (.leaf 3027035770) (.leaf 2948451305)) (.branch 29 (.leaf 2872328388) (.leaf 2798572684)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2727094232) (.branch 32 (.leaf 2657807197) (.leaf 2590629648))) (.branch 35 (.branch 34 (.leaf 2525483343) (.leaf 2462293532)) (.branch 36 (.leaf 2400988774) (.leaf 2341500760)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2283764151) (.leaf 2227716429)) (.branch 40 (.leaf 2173297746) (.leaf 2120450799))) (.branch 43 (.branch 42 (.leaf 2069120692) (.leaf 2019254825)) (.branch 44 (.leaf 1970802780) (.leaf 1923716212))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1877948749) (.branch 47 (.leaf 1833455902) (.leaf 1790194971))) (.branch 50 (.branch 49 (.leaf 1748124964) (.leaf 1707206516)) (.branch 51 (.leaf 1667401812) (.leaf 1628674518)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1590989714) (.leaf 1554313827)) (.branch 55 (.leaf 1518614573) (.leaf 1483860899))) (.branch 58 (.branch 57 (.leaf 1450022926) (.leaf 1417071902)) (.branch 59 (.leaf 1384980147) (.leaf 1353721011))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1323268828) (.branch 62 (.leaf 1293598872) (.leaf 1264687319))) (.branch 65 (.branch 64 (.leaf 1236511209) (.leaf 1209048409)) (.branch 66 (.leaf 1182277576) (.leaf 1156178129)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1130730214) (.leaf 1105914673)) (.branch 70 (.leaf 1081713020) (.leaf 1058107411))) (.branch 73 (.branch 72 (.leaf 1035080616) (.leaf 1012615999)) (.branch 74 (.leaf 990697489) (.leaf 969309564))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 948437223) (.branch 77 (.leaf 928065968) (.leaf 908181787))) (.branch 80 (.branch 79 (.leaf 888771129) (.leaf 869820894)) (.branch 81 (.leaf 851318407) (.leaf 833251409)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 815608039) (.leaf 798376816)) (.branch 85 (.leaf 781546629) (.leaf 765106719))) (.branch 88 (.branch 87 (.leaf 749046670) (.leaf 733356393)) (.branch 89 (.leaf 718026117) (.leaf 703046374)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 688407990) (.branch 92 (.leaf 674102074) (.leaf 660120007))) (.branch 95 (.branch 94 (.leaf 646453434) (.leaf 633094254)) (.branch 96 (.leaf 620034608) (.leaf 607266875)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 594783661) (.leaf 582577790)) (.branch 100 (.leaf 570642302) (.leaf 558970436))) (.branch 103 (.branch 102 (.leaf 547555634) (.leaf 536391524)) (.branch 104 (.leaf 525471922) (.leaf 514790820))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 504342382) (.leaf 494120939)) (.branch 108 (.leaf 484120982) (.leaf 474337157))) (.branch 111 (.branch 110 (.leaf 464764262) (.leaf 455397237)) (.branch 112 (.leaf 446231166) (.leaf 437261267)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 428482889) (.leaf 419891510)) (.branch 116 (.leaf 411482728) (.leaf 403252264))) (.branch 119 (.branch 118 (.leaf 395195953) (.leaf 387309740)) (.branch 120 (.leaf 379589681) (.leaf 372031935)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 978).prefactor = (2480909655519023/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 978).cutoff/(generalMeanRows 978).c)).2 =
    (142237228199777/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 978).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 978).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 978).q*(generalMeanRows 978).c/2-2 = (6041/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable278.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 978).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 978

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 978).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 978).criticalRate j.val*(generalMeanRows 978).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 978).c*(generalMeanRows 978).criticalPoint j.val)).2-
      (generalMeanRows 978).J/2-(generalMeanRows 978).error (generalMeanGrid j.val)+
      (generalMeanRows 978).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 978).c)).2-
      (generalMeanRows 978).J/2-(generalMeanRows 978).error 4 := by
  have he : (generalMeanRows 978).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 978) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 978)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0978

/-! Kernel-checked entropy margins for general spectral rectangle 979. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0979
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6138894099) (.branch 2 (.leaf 5943111856) (.leaf 5755263356))) (.branch 5 (.branch 4 (.leaf 5574932815) (.leaf 5401732839)) (.branch 6 (.leaf 5235301909) (.leaf 5075302152)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4921417342) (.leaf 4773351126)) (.branch 10 (.leaf 4630825426) (.leaf 4493579001))) (.branch 13 (.branch 12 (.leaf 4361366160) (.leaf 4233955585)) (.branch 14 (.leaf 4111129278) (.leaf 3992681595))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3878418373) (.branch 17 (.leaf 3768156127) (.leaf 3661721329))) (.branch 20 (.branch 19 (.leaf 3558949731) (.leaf 3459685757)) (.branch 21 (.leaf 3363781942) (.leaf 3271098410)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3181502398) (.leaf 3094867815)) (.branch 25 (.leaf 3011074838) (.leaf 2930009529))) (.branch 28 (.branch 27 (.leaf 2851563491) (.leaf 2775633540)) (.branch 29 (.leaf 2702121404) (.leaf 2630933444)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2561980392) (.branch 32 (.leaf 2495177105) (.leaf 2430442343))) (.branch 35 (.branch 34 (.leaf 2367698550) (.leaf 2306871661)) (.branch 36 (.leaf 2247890913) (.leaf 2190688670)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2135200264) (.leaf 2081363836)) (.branch 40 (.leaf 2029120195) (.leaf 1978412684))) (.branch 43 (.branch 42 (.leaf 1929187051) (.leaf 1881391326)) (.branch 44 (.leaf 1834975717) (.leaf 1789892493))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1746095891) (.branch 47 (.leaf 1703542020) (.leaf 1662188769))) (.branch 50 (.branch 49 (.leaf 1621995726) (.leaf 1582924095)) (.branch 51 (.leaf 1544936624) (.leaf 1507997530)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1472072435) (.leaf 1437128296)) (.branch 55 (.leaf 1403133354) (.leaf 1370057066))) (.branch 58 (.branch 57 (.leaf 1337870059) (.leaf 1306544071)) (.branch 59 (.leaf 1276051908) (.leaf 1246367394))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1217465327) (.branch 62 (.leaf 1189321437) (.leaf 1161912346))) (.branch 65 (.branch 64 (.leaf 1135215531) (.leaf 1109209286)) (.branch 66 (.leaf 1083872689) (.leaf 1059185567)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1035128468) (.leaf 1011682628)) (.branch 70 (.leaf 988829944) (.leaf 966552948))) (.branch 73 (.branch 72 (.leaf 944834780) (.leaf 923659161)) (.branch 74 (.leaf 903010374) (.leaf 882873241))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 863233097) (.branch 77 (.leaf 844075775) (.leaf 825387583))) (.branch 80 (.branch 79 (.leaf 807155287) (.leaf 789366094)) (.branch 81 (.leaf 772007630) (.leaf 755067932)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 738535426) (.leaf 722398912)) (.branch 85 (.leaf 706647555) (.leaf 691270866))) (.branch 88 (.branch 87 (.leaf 676258692) (.leaf 661601202)) (.branch 89 (.leaf 647288877) (.leaf 633312495)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 619663123) (.branch 92 (.leaf 606332107) (.leaf 593311058))) (.branch 95 (.branch 94 (.leaf 580591847) (.leaf 568166593)) (.branch 96 (.leaf 556027655) (.leaf 544167623)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 532579308) (.leaf 521255741)) (.branch 100 (.leaf 510190155) (.leaf 499375988))) (.branch 103 (.branch 102 (.leaf 488806870) (.leaf 478476615)) (.branch 104 (.leaf 468379223) (.leaf 458508863))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 448859875) (.leaf 439426762)) (.branch 108 (.leaf 430204182) (.leaf 421186946))) (.branch 111 (.branch 110 (.leaf 412370014) (.leaf 403748485)) (.branch 112 (.leaf 395317597) (.leaf 387072720)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 379009353) (.leaf 371123119)) (.branch 116 (.leaf 363409763) (.leaf 355865143))) (.branch 119 (.branch 118 (.leaf 348485234) (.leaf 341266118)) (.branch 120 (.leaf 334203982) (.leaf 327295117)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 979).prefactor = (7910092530001/1600000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 979).cutoff/(generalMeanRows 979).c)).2 =
    (35708739225541/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 979).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 979).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 979).q*(generalMeanRows 979).c/2-2 = (1577/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable272.value]
    have hcontinuation : (generalMeanRows 979).q*(generalMeanRows 979).cutoff/2-2 = (65/38:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable044.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 979).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 979

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 979).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 979).criticalRate j.val*(generalMeanRows 979).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 979).c*(generalMeanRows 979).criticalPoint j.val)).2-
      (generalMeanRows 979).J/2-(generalMeanRows 979).error (generalMeanGrid j.val)+
      (generalMeanRows 979).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 979).c)).2-
      (generalMeanRows 979).J/2-(generalMeanRows 979).error 4 := by
  have he : (generalMeanRows 979).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 979) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 979)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0979

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock13 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 13 i) := by
  fin_cases i
  · exact EntropyRow0910.numerical
  · exact EntropyRow0911.numerical
  · exact EntropyRow0912.numerical
  · exact EntropyRow0913.numerical
  · exact EntropyRow0914.numerical
  · exact EntropyRow0915.numerical
  · exact EntropyRow0916.numerical
  · exact EntropyRow0917.numerical
  · exact EntropyRow0918.numerical
  · exact EntropyRow0919.numerical
  · exact EntropyRow0920.numerical
  · exact EntropyRow0921.numerical
  · exact EntropyRow0922.numerical
  · exact EntropyRow0923.numerical
  · exact EntropyRow0924.numerical
  · exact EntropyRow0925.numerical
  · exact EntropyRow0926.numerical
  · exact EntropyRow0927.numerical
  · exact EntropyRow0928.numerical
  · exact EntropyRow0929.numerical
  · exact EntropyRow0930.numerical
  · exact EntropyRow0931.numerical
  · exact EntropyRow0932.numerical
  · exact EntropyRow0933.numerical
  · exact EntropyRow0934.numerical
  · exact EntropyRow0935.numerical
  · exact EntropyRow0936.numerical
  · exact EntropyRow0937.numerical
  · exact EntropyRow0938.numerical
  · exact EntropyRow0939.numerical
  · exact EntropyRow0940.numerical
  · exact EntropyRow0941.numerical
  · exact EntropyRow0942.numerical
  · exact EntropyRow0943.numerical
  · exact EntropyRow0944.numerical
  · exact EntropyRow0945.numerical
  · exact EntropyRow0946.numerical
  · exact EntropyRow0947.numerical
  · exact EntropyRow0948.numerical
  · exact EntropyRow0949.numerical
  · exact EntropyRow0950.numerical
  · exact EntropyRow0951.numerical
  · exact EntropyRow0952.numerical
  · exact EntropyRow0953.numerical
  · exact EntropyRow0954.numerical
  · exact EntropyRow0955.numerical
  · exact EntropyRow0956.numerical
  · exact EntropyRow0957.numerical
  · exact EntropyRow0958.numerical
  · exact EntropyRow0959.numerical
  · exact EntropyRow0960.numerical
  · exact EntropyRow0961.numerical
  · exact EntropyRow0962.numerical
  · exact EntropyRow0963.numerical
  · exact EntropyRow0964.numerical
  · exact EntropyRow0965.numerical
  · exact EntropyRow0966.numerical
  · exact EntropyRow0967.numerical
  · exact EntropyRow0968.numerical
  · exact EntropyRow0969.numerical
  · exact EntropyRow0970.numerical
  · exact EntropyRow0971.numerical
  · exact EntropyRow0972.numerical
  · exact EntropyRow0973.numerical
  · exact EntropyRow0974.numerical
  · exact EntropyRow0975.numerical
  · exact EntropyRow0976.numerical
  · exact EntropyRow0977.numerical
  · exact EntropyRow0978.numerical
  · exact EntropyRow0979.numerical
end SingularValueBounds.KL.Certificates
