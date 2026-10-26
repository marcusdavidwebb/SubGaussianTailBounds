import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 420. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0420
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5004340690, 4832554240, 4668529413, 4511819780, 4362010572, 4218715921, 4081576390, 3950256770, 3824444095, 3703845863, 3588188422, 3477215514, 3370686954, 3268377433, 3170075420, 3075582169, 2984710805, 2897285492, 2813140667, 2732120335, 2654077427, 2578873201, 2506376698, 2436464227, 2369018905, 2303930217, 2241093619, 2180410159, 2121786138, 2065132784, 2010365954, 1957405854, 1906176785, 1856606894, 1808627952, 1762175144, 1717186871, 1673604565, 1631372519, 1590437723, 1550749717, 1512260443, 1474924121, 1438697115, 1403537825, 1369406570, 1336265489, 1304078444, 1272810926, 1242429971, 1212904082, 1184203147, 1156298371, 1129162210, 1102768303, 1077091417, 1052107385, 1027793058, 1004126251, 981085695, 958650996, 936802587, 915521694, 894790291, 874591071, 854907407, 835723322, 817023457, 798793046, 781017883, 763684300, 746779143, 730289745, 714203907, 698509876, 683196328, 668252342, 653667390, 639431315, 625534317, 611966939, 598720048, 585784824, 573152748, 560815588, 548765386, 536994449, 525495337, 514260850, 503284026, 492558123, 482076614, 471833179, 461821697, 452036237, 442471050, 433120564, 423979377, 415042250, 406304100, 397759996, 389405153, 381234925, 373244801, 365430403, 357787476, 350311888, 342999621, 335846774, 328849551, 322004265, 315307328, 308755251, 302344640, 296072193, 289934696, 283929021, 278052124, 272301039, 266672881, 261164839]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 420).prefactor = (1192784052154809/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 420).cutoff/(generalMeanRows 420).c)).2 =
    (96222215879131/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 420).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 420).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 420).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 420

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 420).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 420).criticalRate j.val*(generalMeanRows 420).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 420).c*(generalMeanRows 420).criticalPoint j.val)).2-
      (generalMeanRows 420).J/2-(generalMeanRows 420).error (generalMeanGrid j.val)+
      (generalMeanRows 420).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 420).c)).2-
      (generalMeanRows 420).J/2-(generalMeanRows 420).error 4 := by
  have he : (generalMeanRows 420).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 420) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 420)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0420

/-! Kernel-checked entropy margins for general spectral rectangle 421. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0421
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4997170041, 4825651117, 4661874365, 4505394997, 4355799746, 4212704119, 4075749938, 3944603151, 3818951849, 3698504498, 3582988335, 3472147916, 3365743803, 3263551370, 3165359711, 3070970654, 2980197851, 2892865944, 2808809812, 2727873862, 2649911394, 2574784004, 2502361037, 2432519086, 2365141523, 2300118069, 2237344390, 2176721732, 2118156572, 2061560298, 2006848914, 1953942760, 1902766256, 1853247658, 1805318839, 1758915071, 1713974836, 1670439641, 1628253842, 1587364491, 1547721178, 1509275896, 1471982904, 1435798608, 1400681439, 1366591748, 1333491700, 1301345180, 1270117702, 1239776319, 1210289550, 1181627298, 1153760779, 1126662461, 1100305992, 1074666146, 1049718764, 1025440702, 1001809779, 978804731, 956405168, 934591524, 913345028, 892647657, 872482103, 852831742, 833680596, 815013308, 796815111, 779071801, 761769710, 744895682, 728437053, 712381622, 696717637, 681433773, 666519111, 651963121, 637755649, 623886894, 610347398, 597128030, 584219972, 571614704, 559303994, 547279888, 535534692, 524060966, 512851516, 501899377, 491197810, 480740290, 470520499, 460532318, 450769817, 441227250, 431899047, 422779809, 413864298, 405147435, 396624291, 388290083, 380140168, 372170039, 364375320, 356751758, 349295225, 342001707, 334867304, 327888226, 321060786, 314381402, 307846586, 301452949, 295197191, 289076102, 283086557, 277225516, 271490017, 265877178, 260384189]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 421).prefactor = (594491010633323/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 421).cutoff/(generalMeanRows 421).c)).2 =
    (191711830894597/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 421).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 421).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 421).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 421

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 421).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 421).criticalRate j.val*(generalMeanRows 421).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 421).c*(generalMeanRows 421).criticalPoint j.val)).2-
      (generalMeanRows 421).J/2-(generalMeanRows 421).error (generalMeanGrid j.val)+
      (generalMeanRows 421).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 421).c)).2-
      (generalMeanRows 421).J/2-(generalMeanRows 421).error 4 := by
  have he : (generalMeanRows 421).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 421) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 421)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0421

/-! Kernel-checked entropy margins for general spectral rectangle 422. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0422
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5005785720, 4833971078, 4669911957, 4513162801, 4363309631, 4219967291, 4082776986, 3951404087, 3825536148, 3704881133, 3589165807, 3478134287, 3371546721, 3269178096, 3170817144, 3076265350, 2985336044, 2897853568, 2813652514, 2732577021, 2654480137, 2579223219, 2506675386, 2436713020, 2369219291, 2304083729, 2241201821, 2180474643, 2121808510, 2065114658, 2010308945, 1957311575, 1906046837, 1856442864, 1808431410, 1761947637, 1716929920, 1673319665, 1631061134, 1590101284, 1550389622, 1511878056, 1474520767, 1438274085, 1403096370, 1368947904, 1335790788, 1303588845, 1272307526, 1241913832, 1212376224, 1183664555, 1155749992, 1128604953, 1102203043, 1076518990, 1051528596, 1027208676, 1003537011, 980492300, 958054117, 936202865, 914919737, 894186681, 873986360, 854302119, 835117954, 816418482, 798188910, 780415008, 763083086, 746179966, 729692959, 713609847, 697918856, 682608641, 667668264, 653087178, 638855211, 624962544, 611399705, 598157545, 585227232, 572600231, 560268297, 548223460, 536458013, 524964506, 513735729, 502764707, 492044690, 481569140, 471331729, 461326327, 451546994, 441987975, 432643690, 423508729, 414577847, 405845955, 397308115, 388959538, 380795572, 372811702, 365003543, 357366838, 349897449, 342591356, 335444653, 328453542, 321614331, 314923430, 308377348, 301972687, 295706143, 289574501, 283574630, 277703484, 271958096, 266335579, 260833120]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 422).prefactor = (297757989745873/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 422).cutoff/(generalMeanRows 422).c)).2 =
    (191711830894597/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 422).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 422).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 422).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 422

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 422).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 422).criticalRate j.val*(generalMeanRows 422).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 422).c*(generalMeanRows 422).criticalPoint j.val)).2-
      (generalMeanRows 422).J/2-(generalMeanRows 422).error (generalMeanGrid j.val)+
      (generalMeanRows 422).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 422).c)).2-
      (generalMeanRows 422).J/2-(generalMeanRows 422).error 4 := by
  have he : (generalMeanRows 422).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 422) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 422)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0422

/-! Kernel-checked entropy margins for general spectral rectangle 423. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0423
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4932186803, 4760544223, 4596672094, 4440124799, 4290488249, 4147377139, 4010432488, 3879319444, 3753725316, 3633357791, 3517943338, 3407225756, 3300964862, 3198935292, 3100925420, 3006736360, 2916181062, 2829083485, 2745277829, 2664607842, 2586926174, 2512093785, 2439979400, 2370459003, 2303415371, 2238737644, 2176320921, 2116065894, 2057878501, 2001669603, 1947354692, 1894853610, 1844090289, 1794992516, 1747491702, 1701522676, 1657023485, 1613935215, 1572201816, 1531769944, 1492588806, 1454610023, 1417787496, 1382077282, 1347437476, 1313828104, 1281211016, 1249549794, 1218809658, 1188957378, 1159961201, 1131790765, 1104417036, 1077812234, 1051949773, 1026804202, 1002351143, 978567244, 955430122, 932918322, 911011267, 889689216, 868933225, 848725110, 829047407, 809883343, 791216798, 773032278, 755314887, 738050297, 721224721, 704824894, 688838041, 673251863, 658054511, 643234568, 628781029, 614683283, 600931098, 587514601, 574424266, 561650897, 549185615, 537019845, 525145302, 513553981, 502238144, 491190310, 480403242, 469869942, 459583637, 449537772, 439726002, 430142182, 420780361, 411634774, 402699833, 393970124, 385440396, 377105561, 368960679, 361000963, 353221765, 345618574, 338187013, 330922832, 323821901, 316880214, 310093873, 303459097, 296972205, 290629625, 284427880, 278363591, 272433473, 266634329, 260963049, 255416607, 249992060, 244686542, 239497263]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 423).prefactor = (4765295928651677/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 423).cutoff/(generalMeanRows 423).c)).2 =
    (74865395776473/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 423).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 423).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 423).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 423

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 423).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 423).criticalRate j.val*(generalMeanRows 423).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 423).c*(generalMeanRows 423).criticalPoint j.val)).2-
      (generalMeanRows 423).J/2-(generalMeanRows 423).error (generalMeanGrid j.val)+
      (generalMeanRows 423).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 423).c)).2-
      (generalMeanRows 423).J/2-(generalMeanRows 423).error 4 := by
  have he : (generalMeanRows 423).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 423) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 423)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0423

/-! Kernel-checked entropy margins for general spectral rectangle 424. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0424
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4940725059, 4768785344, 4604629531, 4447811232, 4297915642, 4154556788, 4017375068, 3886035051, 3760223502, 3639647605, 3524033355, 3413124107, 3306679261, 3204473065, 3106293525, 3011941411, 2921229351, 2833980996, 2750030262, 2669220625, 2591404480, 2516442546, 2444203322, 2374562576, 2307402883, 2242613190, 2180088416, 2119729080, 2061440956, 2005134753, 1950725816, 1898133848, 1847282649, 1798099882, 1750516838, 1704468233, 1659892008, 1616729146, 1574923502, 1534421637, 1495172671, 1457128142, 1420241871, 1384469837, 1349770066, 1316102511, 1283428959, 1251712927, 1220919575, 1191015618, 1161969245, 1133750042, 1106328925, 1079678067, 1053770835, 1028581734, 1004086343, 980261271, 957084096, 934533325, 912588346, 891229383, 870437462, 850194364, 830482596, 811285356, 792586497, 774370497, 756622435, 739327958, 722473255, 706045037, 690030509, 674417349, 659193689, 644348091, 629869531, 615747380, 601971388, 588531665, 575418669, 562623188, 550136327, 537949496, 526054397, 514443010, 503107584, 492040624, 481234882, 470683348, 460379236, 450315980, 440487225, 430886814, 421508787, 412347367, 403396959, 394652137, 386107644, 377758379, 369599398, 361625903, 353833238, 346216885, 338772459, 331495702, 324382479, 317428774, 310630686, 303984424, 297486303, 291132742, 284920261, 278845475, 272905091, 267095908, 261414810, 255858767, 250424829, 245110126, 239911864]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 424).prefactor = (11933863188181/2500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 424).cutoff/(generalMeanRows 424).c)).2 =
    (74865395776473/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 424).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 424).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 424).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 424

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 424).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 424).criticalRate j.val*(generalMeanRows 424).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 424).c*(generalMeanRows 424).criticalPoint j.val)).2-
      (generalMeanRows 424).J/2-(generalMeanRows 424).error (generalMeanGrid j.val)+
      (generalMeanRows 424).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 424).c)).2-
      (generalMeanRows 424).J/2-(generalMeanRows 424).error 4 := by
  have he : (generalMeanRows 424).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 424) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 424)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0424

/-! Kernel-checked entropy margins for general spectral rectangle 425. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0425
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4875616412, 4703609228, 4539420204, 4382601205, 4232735777, 4089436384, 3952341942, 3821115615, 3695442831, 3575029501, 3459600410, 3348897759, 3242679847, 3140719868, 3042804825, 2948734527, 2858320683, 2771386063, 2687763741, 2607296385, 2529835616, 2455241412, 2383381557, 2314131138, 2247372074, 2182992682, 2120887276, 2060955794, 2003103455, 1947240430, 1893281548, 1841146020, 1790757171, 1742042205, 1694931976, 1649360779, 1605266150, 1562588683, 1521271858, 1481261878, 1442507520, 1404959989, 1368572789, 1333301595, 1299104137, 1265940092, 1233770975, 1202560045, 1172272215, 1142873962, 1114333247, 1086619441, 1059703250, 1033556646, 1008152809, 983466058, 959471800, 936146476, 913467507, 891413246, 869962938, 849096670, 828795334, 809040589, 789814823, 771101120, 752883226, 735145519, 717872981, 701051168, 684666183, 668704657, 653153718, 638000971, 623234481, 608842747, 594814686, 581139613, 567807226, 554807587, 542131109, 529768538, 517710944, 505949700, 494476476, 483283223, 472362165, 461705783, 451306808, 441158211, 431253190, 421585168, 412147774, 402934846, 393940414, 385158697, 376584096, 368211184, 360034703, 352049555, 344250798, 336633640, 329193432, 321925662, 314825956, 307890066, 301113867, 294493358, 288024651, 281703969, 275527644, 269492114, 263593913, 257829677, 252196133, 246690099, 241308481, 236048271, 230906542, 225880445, 220967212]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 425).prefactor = (1197521708827301/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 425).cutoff/(generalMeanRows 425).c)).2 =
    (73350237014781/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 425).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 425).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 425).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 425

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 425).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 425).criticalRate j.val*(generalMeanRows 425).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 425).c*(generalMeanRows 425).criticalPoint j.val)).2-
      (generalMeanRows 425).J/2-(generalMeanRows 425).error (generalMeanGrid j.val)+
      (generalMeanRows 425).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 425).c)).2-
      (generalMeanRows 425).J/2-(generalMeanRows 425).error 4 := by
  have he : (generalMeanRows 425).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 425) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 425)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0425

/-! Kernel-checked entropy margins for general spectral rectangle 426. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0426
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5287756796, 5118827692, 4957416142, 4803086089, 4655432630, 4514079296, 4378675620, 4248894963, 4124432563, 4005003771, 3890342465, 3780199614, 3674341974, 3572550905, 3474621290, 3380360553, 3289587759, 3202132792, 3117835598, 3036545495, 2958120532, 2882426902, 2809338404, 2738735940, 2670507054, 2604545505, 2540750869, 2479028173, 2419287557, 2361443952, 2305416790, 2251129727, 2198510391, 2147490140, 2098003847, 2049989686, 2003388942, 1958145830, 1914207328, 1871523016, 1830044929, 1789727420, 1750527027, 1712402355, 1675313960, 1639224240, 1604097339, 1569899047, 1536596716, 1504159173, 1472556643, 1441760676, 1411744075, 1382480832, 1353946067, 1326115968, 1298967739, 1272479544, 1246630463, 1221400443, 1196770256, 1172721457, 1149236346, 1126297931, 1103889896, 1081996563, 1060602866, 1039694321, 1019256996, 999277487, 979742893, 960640792, 941959219, 923686647, 905811962, 888324450, 871213776, 854469968, 838083399, 822044774, 806345116, 790975751, 775928292, 761194634, 746766935, 732637609, 718799313, 705244938, 691967602, 678960634, 666217573, 653732155, 641498305, 629510133, 617761924, 606248130, 594963370, 583902413, 573060184, 562431749, 552012315, 541797222, 531781941, 521962065, 512333310, 502891506, 493632595, 484552627, 475647757, 466914239, 458348425, 449946761, 441705784, 433622119, 425692474, 417913641, 410282490, 402795971, 395451104, 388244985, 381174778]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 426).prefactor = (4684908428220809/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 426).cutoff/(generalMeanRows 426).c)).2 =
    (106799093155119/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 426).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 426).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 426).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 426

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 426).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 426).criticalRate j.val*(generalMeanRows 426).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 426).c*(generalMeanRows 426).criticalPoint j.val)).2-
      (generalMeanRows 426).J/2-(generalMeanRows 426).error (generalMeanGrid j.val)+
      (generalMeanRows 426).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 426).c)).2-
      (generalMeanRows 426).J/2-(generalMeanRows 426).error 4 := by
  have he : (generalMeanRows 426).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 426) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 426)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0426

/-! Kernel-checked entropy margins for general spectral rectangle 427. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0427
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4950790205, 4778528166, 4614057164, 4456930919, 4306734706, 4163082605, 4025615042, 3893996592, 3767914007, 3647074436, 3531203828, 3420045474, 3313358699, 3210917662, 3112510273, 3017937196, 2927010944, 2839555050, 2755403302, 2674399047, 2596394546, 2521250381, 2448834910, 2379023760, 2311699363, 2246750524, 2184072017, 2123564218, 2065132759, 2008688206, 1954145762, 1901424991, 1850449557, 1801146984, 1753448431, 1707288481, 1662604946, 1619338683, 1577433419, 1536835596, 1497494214, 1459360693, 1422388741, 1386534227, 1351755066, 1318011107, 1285264035, 1253477265, 1222615861, 1192646443, 1163537108, 1135257354, 1107778010, 1081071164, 1055110103, 1029869253, 1005324117, 981451229, 958228098, 935633159, 913645735, 892245985, 871414872, 851134118, 831386171, 812154172, 793421921, 775173843, 757394967, 740070890, 723187755, 706732228, 690691470, 675053117, 659805260, 644936422, 630435542, 616291955, 602495376, 589035881, 575903896, 563090177, 550585800, 538382148, 526470892, 514843988, 503493659, 492412384, 481592894, 471028153, 460711356, 450635916, 440795455, 431183800, 421794970, 412623173, 403662794, 394908392, 386354693, 377996584, 369829102, 361847438, 354046922, 346423023, 338971344, 331687615, 324567690, 317607541, 310803256, 304151036, 297647185, 291288115, 285070334, 278990449, 273045161, 267231259, 261545621, 255985210, 250547068, 245228318, 240026161]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 427).prefactor = (2387373473241211/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 427).cutoff/(generalMeanRows 427).c)).2 =
    (372866058242689/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 427).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 427).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 427).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 427

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 427).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 427).criticalRate j.val*(generalMeanRows 427).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 427).c*(generalMeanRows 427).criticalPoint j.val)).2-
      (generalMeanRows 427).J/2-(generalMeanRows 427).error (generalMeanGrid j.val)+
      (generalMeanRows 427).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 427).c)).2-
      (generalMeanRows 427).J/2-(generalMeanRows 427).error 4 := by
  have he : (generalMeanRows 427).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 427) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 427)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0427

/-! Kernel-checked entropy margins for general spectral rectangle 428. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0428
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4877248733, 4705215895, 4540994902, 4384138498, 4234231023, 4090885660, 3953741973, 3822463709, 3696736825, 3576267703, 3460781552, 3350020954, 3243744546, 3141725827, 3043752066, 2949623312, 2859151482, 2772159532, 2688480696, 2607957784, 2530442537, 2455795037, 2383883155, 2314582051, 2247773706, 2183346484, 2121194739, 2061218437, 2003322817, 1947418062, 1893419009, 1841244866, 1790818952, 1742068463, 1694924236, 1649320548, 1605194912, 1562487898, 1521142959, 1481106269, 1442326572, 1404755043, 1368345150, 1333052535, 1298834892, 1265651861, 1233464922, 1202237296, 1171933860, 1142521055, 1113966805, 1086240444, 1059312642, 1033155337, 1007741673, 983045935, 959043496, 935710764, 913025127, 890964908, 869509319, 848638417, 828333066, 808574896, 789346266, 770630234, 752410520, 734671477, 717398061, 700575804, 684190789, 668229622, 652679409, 637527738, 622762650, 608372628, 594346569, 580673770, 567343913, 554347044, 541673558, 529314190, 517259991, 505502323, 494032842, 482843488, 471926469, 461274258, 450879574, 440735377, 430834856, 421171423, 411738699, 402530513, 393540886, 384764031, 376194340, 367826379, 359654884, 351674751, 343881032, 336268928, 328833785, 321571088, 314476455, 307545635, 300774500, 294159043, 287695373, 281379710, 275208384, 269177826, 263284571, 257525250, 251896588, 246395402, 241018594, 235763155, 230626156, 225604747, 220696157]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 428).prefactor = (239152319790583/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 428).cutoff/(generalMeanRows 428).c)).2 =
    (365290264434231/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 428).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 428).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 428).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 428

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 428).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 428).criticalRate j.val*(generalMeanRows 428).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 428).c*(generalMeanRows 428).criticalPoint j.val)).2-
      (generalMeanRows 428).J/2-(generalMeanRows 428).error (generalMeanGrid j.val)+
      (generalMeanRows 428).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 428).c)).2-
      (generalMeanRows 428).J/2-(generalMeanRows 428).error 4 := by
  have he : (generalMeanRows 428).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 428) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 428)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0428

/-! Kernel-checked entropy margins for general spectral rectangle 429. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0429
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4887331643, 4714976340, 4550440014, 4393275517, 4243067267, 4099428497, 3961998799, 3830441927, 3704443819, 3583710828, 3467968113, 3356958192, 3250439628, 3148185831, 3049983974, 2955634001, 2864947714, 2777747951, 2693867821, 2613150003, 2535446104, 2460616070, 2388527634, 2319055815, 2252082450, 2187495762, 2125189961, 2065064872, 2007025588, 1950982155, 1896849266, 1844545990, 1793995512, 1745124889, 1697864826, 1652149467, 1607916198, 1565105461, 1523660585, 1483527621, 1444655197, 1406994368, 1370498492, 1335123096, 1300825770, 1267566045, 1235305300, 1204006657, 1173634895, 1144156359, 1115538883, 1087751713, 1060765432, 1034551893, 1009084159, 984336437, 960284025, 936903254, 914171444, 892066846, 870568607, 849656719, 829311983, 809515969, 790250979, 771500012, 753246736, 735475450, 718171060, 701319051, 684905455, 668916836, 653340256, 638163259, 623373847, 608960463, 594911966, 581217619, 567867066, 554850321, 542157748, 529780047, 517708242, 505933666, 494447947, 483242997, 472311001, 461644405, 451235905, 441078438, 431165172, 421489497, 412045015, 402825534, 393825059, 385037781, 376458078, 368080499, 359899763, 351910751, 344108501, 336488200, 329045180, 321774913, 314673006, 307735194, 300957340, 294335423, 287865544, 281543911, 275366845, 269330769, 263432207, 257667783, 252034214, 246528307, 241146958, 235887151, 230745949, 225720497, 220808016]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 429).prefactor = (956856468625323/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 429).cutoff/(generalMeanRows 429).c)).2 =
    (363831474970569/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 429).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 429).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 429).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 429

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 429).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 429).criticalRate j.val*(generalMeanRows 429).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 429).c*(generalMeanRows 429).criticalPoint j.val)).2-
      (generalMeanRows 429).J/2-(generalMeanRows 429).error (generalMeanGrid j.val)+
      (generalMeanRows 429).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 429).c)).2-
      (generalMeanRows 429).J/2-(generalMeanRows 429).error 4 := by
  have he : (generalMeanRows 429).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 429) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 429)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0429

/-! Kernel-checked entropy margins for general spectral rectangle 430. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0430
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5271810749, 5103382947, 4942436662, 4788538961, 4641287801, 4500309324, 4365255452, 4235801732, 4111645399, 3992503631, 3878111979, 3768222939, 3662604664, 3561039791, 3463324369, 3369266889, 3278687390, 3191416644, 3107295409, 3026173740, 2947910362, 2872372082, 2799433257, 2728975298, 2660886210, 2595060173, 2531397143, 2469802493, 2410186674, 2352464901, 2296556860, 2242386438, 2189881470, 2138973502, 2089597573, 2041692008, 1995198225, 1950060561, 1906226100, 1863644515, 1822267926, 1782050761, 1742949622, 1704923172, 1667932016, 1631938596, 1596907092, 1562803328, 1529594682, 1497250005, 1465739540, 1435034852, 1405108759, 1375935263, 1347489490, 1319747635, 1292686906, 1266285469, 1240522405, 1215377662, 1190832010, 1166867003, 1143464938, 1120608821, 1098282331, 1076469788, 1055156122, 1034326844, 1013968019, 994066239, 974608599, 955582673, 936976494, 918778528, 900977662, 883563177, 866524736, 849852365, 833536434, 817567648, 801937027, 786635897, 771655871, 756988843, 742626972, 728562671, 714788599, 701297650, 688082939, 675137802, 662455776, 650030601, 637856206, 625926704, 614236381, 602779696, 591551269, 580545876, 569758445, 559184046, 548817892, 538655328, 528691830, 518922997, 509344550, 499952326, 490742272, 481710445, 472853005, 464166214, 455646430, 447290106, 439093786, 431054100, 423167765, 415431579, 407842420, 400397243, 393093079, 385927028, 378896263]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 430).prefactor = (4655765056926483/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 430).cutoff/(generalMeanRows 430).c)).2 =
    (212138331258571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 430).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 430).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 430).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 430

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 430).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 430).criticalRate j.val*(generalMeanRows 430).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 430).c*(generalMeanRows 430).criticalPoint j.val)).2-
      (generalMeanRows 430).J/2-(generalMeanRows 430).error (generalMeanGrid j.val)+
      (generalMeanRows 430).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 430).c)).2-
      (generalMeanRows 430).J/2-(generalMeanRows 430).error 4 := by
  have he : (generalMeanRows 430).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 430) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 430)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0430

/-! Kernel-checked entropy margins for general spectral rectangle 431. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0431
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5262145477, 5094029930, 4933388891, 4779789317, 4632829082, 4492134277, 4357356797, 4228172182, 4104277684, 3985390514, 3871246273, 3761597523, 3656212494, 3554873911, 3457377924, 3363533131, 3273159686, 3186088483, 3102160407, 3021225645, 2943143056, 2867779586, 2795009733, 2724715049, 2656783684, 2591109958, 2527593974, 2466141247, 2406662372, 2349072703, 2293292069, 2239244495, 2186857954, 2136064125, 2086798181, 2038998577, 1992606861, 1947567495, 1903827684, 1861337225, 1820048353, 1779915611, 1740895715, 1702947435, 1666031484, 1630110408, 1595148486, 1561111640, 1527967344, 1495684541, 1464233564, 1433586065, 1403714945, 1374594288, 1346199300, 1318506251, 1291492424, 1265136056, 1239416299, 1214313165, 1189807489, 1165880889, 1142515722, 1119695051, 1097402612, 1075622778, 1054340532, 1033541436, 1013211602, 993337669, 973906778, 954906546, 936325046, 918150787, 900372692, 882980080, 865962651, 849310463, 833013922, 817063763, 801451038, 786167101, 771203594, 756552437, 742205816, 728156170, 714396181, 700918765, 687717063, 674784428, 662114420, 649700799, 637537511, 625618687, 613938633, 602491823, 591272893, 580276635, 569497990, 558932044, 548574023, 538419285, 528463318, 518701734, 509130265, 499744758, 490541172, 481515573, 472664132, 463983119, 455468902, 447117941, 438926789, 430892085, 423010552, 415278995, 407694301, 400253430, 392953418, 385791374, 378764475]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 431).prefactor = (4654720645481781/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 431).cutoff/(generalMeanRows 431).c)).2 =
    (212867725990401/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 431).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 431).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 431).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 431

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 431).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 431).criticalRate j.val*(generalMeanRows 431).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 431).c*(generalMeanRows 431).criticalPoint j.val)).2-
      (generalMeanRows 431).J/2-(generalMeanRows 431).error (generalMeanGrid j.val)+
      (generalMeanRows 431).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 431).c)).2-
      (generalMeanRows 431).J/2-(generalMeanRows 431).error 4 := by
  have he : (generalMeanRows 431).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 431) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 431)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0431

/-! Kernel-checked entropy margins for general spectral rectangle 432. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0432
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4894218704, 4721587293, 4556794907, 4399392734, 4248963669, 4105119548, 3967498681, 3835763646, 3709599305, 3588711021, 3472823046, 3361677066, 3255030879, 3152657194, 3054342542, 2959886275, 2869099655, 2781805025, 2697835036, 2617031951, 2539246996, 2464339766, 2392177673, 2322635442, 2255594642, 2190943252, 2128575255, 2068390271, 2010293208, 1954193937, 1900006999, 1847651320, 1797049954, 1748129841, 1700821580, 1655059218, 1610780050, 1567924441, 1526435646, 1486259652, 1447345024, 1409642768, 1373106190, 1337690777, 1303354077, 1270055589, 1237756657, 1206420378, 1176011504, 1146496359, 1117842757, 1090019925, 1062998430, 1036750113, 1011248024, 986466359, 962380406, 938966490, 916201920, 894064944, 872534702, 851591182, 831215181, 811388263, 792092729, 773311577, 755028469, 737227704, 719894186, 703013398, 686571373, 670554670, 654950351, 639745961, 624929500, 610489409, 596414547, 582694175, 569317938, 556275847, 543558265, 531155893, 519059753, 507261175, 495751787, 484523500, 473568497, 462879223, 452448371, 442268878, 432333909, 422636853, 413171309, 403931083, 394910178, 386102785, 377503276, 369106200, 360906273, 352898374, 345077537, 337438947, 329977934, 322689967, 315570649, 308615714, 301821019, 295182545, 288696385, 282358747, 276165948, 270114407, 264200647, 258421287, 252773041, 247252713, 241857198, 236583473, 231428600, 226389720, 221464051]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 432).prefactor = (4799688597771513/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 432).cutoff/(generalMeanRows 432).c)).2 =
    (365290264434231/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 432).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 432).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 432).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 432

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 432).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 432).criticalRate j.val*(generalMeanRows 432).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 432).c*(generalMeanRows 432).criticalPoint j.val)).2-
      (generalMeanRows 432).J/2-(generalMeanRows 432).error (generalMeanGrid j.val)+
      (generalMeanRows 432).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 432).c)).2-
      (generalMeanRows 432).J/2-(generalMeanRows 432).error 4 := by
  have he : (generalMeanRows 432).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 432) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 432)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0432

/-! Kernel-checked entropy margins for general spectral rectangle 433. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0433
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5280705626, 5111993644, 4950775801, 4796618437, 4649118827, 4507902483, 4372620741, 4242948600, 4118582784, 3999239994, 3884655334, 3774580883, 3668784404, 3567048165, 3469167872, 3374951694, 3284219364, 3196801370, 3112538201, 3031279660, 2952884232, 2877218499, 2804156608, 2733579769, 2665375798, 2599438695, 2535668249, 2473969674, 2414253268, 2356434103, 2300431731, 2246169910, 2193576353, 2142582491, 2093123253, 2045136858, 1998564629, 1953350806, 1909442385, 1866788954, 1825342553, 1785057531, 1745890418, 1707799808, 1670746238, 1634692089, 1599601478, 1565440172, 1532175495, 1499776244, 1468212613, 1437456119, 1407479533, 1378256813, 1349763045, 1321974383, 1294867995, 1268422013, 1242615480, 1217428312, 1192841245, 1168835802, 1145394252, 1122499571, 1100135411, 1078286064, 1056936437, 1036072015, 1015678839, 995743480, 976253010, 957194983, 938557410, 920328740, 902497839, 885053972, 867986783, 851286280, 834942820, 818947091, 803290098, 787963150, 772957850, 758266075, 743879971, 729791940, 715994628, 702480916, 689243909, 676276930, 663573506, 651127367, 638932431, 626982800, 615272753, 603796738, 592549366, 581525404, 570719771, 560127531, 549743886, 539564176, 529583867, 519798551, 510203943, 500795872, 491570278, 482523212, 473650828, 464949380, 456415221, 448044798, 439834648, 431781397, 423881756, 416132517, 408530553, 401072815, 393756326, 386578184, 379535556]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 433).prefactor = (4663620509236881/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 433).cutoff/(generalMeanRows 433).c)).2 =
    (212138331258571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 433).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 433).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 433).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 433

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 433).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 433).criticalRate j.val*(generalMeanRows 433).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 433).c*(generalMeanRows 433).criticalPoint j.val)).2-
      (generalMeanRows 433).J/2-(generalMeanRows 433).error (generalMeanGrid j.val)+
      (generalMeanRows 433).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 433).c)).2-
      (generalMeanRows 433).J/2-(generalMeanRows 433).error 4 := by
  have he : (generalMeanRows 433).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 433) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 433)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0433

/-! Kernel-checked entropy margins for general spectral rectangle 434. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0434
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5199271467, 5030587869, 4869421195, 4715336995, 4567931786, 4426830344, 4291683293, 4162164941, 4037971343, 3918818551, 3804441036, 3694590264, 3589033399, 3487552128, 3389941591, 3296009404, 3205574762, 3118467630, 3034527985, 2953605132, 2875557069, 2800249906, 2727557326, 2657360088, 2589545570, 2524007343, 2460644776, 2399362676, 2340070944, 2282684264, 2227121810, 2173306972, 2121167103, 2070633284, 2021640105, 1974125453, 1928030326, 1883298651, 1839877116, 1797715012, 1756764089, 1716978414, 1678314242, 1640729899, 1604185665, 1568643666, 1534067777, 1500423526, 1467678004, 1435799786, 1404758848, 1374526495, 1345075293, 1316379003, 1288412516, 1261151801, 1234573845, 1208656604, 1183378954, 1158720644, 1134662253, 1111185150, 1088271456, 1065904004, 1044066306, 1022742523, 1001917430, 981576390, 961705324, 942290686, 923319437, 904779024, 886657356, 868942781, 851624071, 834690398, 818131319, 801936759, 786096991, 770602628, 755444599, 740614145, 726102798, 711902372, 698004952, 684402879, 671088745, 658055375, 645295827, 632803372, 620571496, 608593883, 596864411, 585377144, 574126324, 563106367, 552311850, 541737512, 531378245, 521229085, 511285213, 501541944, 491994726, 482639132, 473470861, 464485724, 455679651, 447048680, 438588953, 430296716, 422168314, 414200188, 406388869, 398730980, 391223229, 383862407, 376645386, 369569118, 362630628, 355827017, 349155455]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 434).prefactor = (291968075980041/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 434).cutoff/(generalMeanRows 434).c)).2 =
    (8329282455607/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 434).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 434).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 434).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 434

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 434).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 434).criticalRate j.val*(generalMeanRows 434).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 434).c*(generalMeanRows 434).criticalPoint j.val)).2-
      (generalMeanRows 434).J/2-(generalMeanRows 434).error (generalMeanGrid j.val)+
      (generalMeanRows 434).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 434).c)).2-
      (generalMeanRows 434).J/2-(generalMeanRows 434).error 4 := by
  have he : (generalMeanRows 434).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 434) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 434)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0434

/-! Kernel-checked entropy margins for general spectral rectangle 435. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0435
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5130292615, 4961334947, 4799917983, 4645607400, 4497999756, 4356719799, 4221418053, 4091768669, 3967467486, 3848230296, 3733791265, 3623901514, 3518327831, 3416851496, 3319267216, 3225382152, 3135015027, 3047995313, 2964162486, 2883365336, 2805461339, 2730316075, 2657802695, 2587801421, 2520199092, 2454888742, 2391769204, 2330744751, 2271724754, 2214623372, 2159359257, 2105855286, 2054038304, 2003838894, 1955191150, 1908032477, 1862303397, 1817947372, 1774910631, 1733142018, 1692592844, 1653216748, 1614969569, 1577809221, 1541695588, 1506590407, 1472457174, 1439261050, 1406968768, 1375548554, 1344970045, 1315204219, 1286223322, 1258000805, 1230511262, 1203730367, 1177634829, 1152202329, 1127411480, 1103241776, 1079673551, 1056687935, 1034266817, 1012392810, 991049212, 970219976, 949889680, 930043494, 910667154, 891746937, 873269634, 855222528, 837593368, 820370353, 803542108, 787097667, 771026453, 755318262, 739963247, 724951900, 710275043, 695923806, 681889620, 668164203, 654739545, 641607901, 628761776, 616193920, 603897310, 591865149, 580090852, 568568040, 557290531, 546252330, 535447627, 524870785, 514516335, 504378972, 494453543, 484735048, 475218630, 465899572, 456773290, 447835330, 439081362, 430507176, 422108678, 413881887, 405822928, 397928031, 390193528, 382615847, 375191510, 367917131, 360789410, 353805135, 346961174, 340254475, 333682063, 327241040, 320928578]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 435).prefactor = (46737042552801/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 435).cutoff/(generalMeanRows 435).c)).2 =
    (40580093576857/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 435).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 435).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 435).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 435

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 435).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 435).criticalRate j.val*(generalMeanRows 435).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 435).c*(generalMeanRows 435).criticalPoint j.val)).2-
      (generalMeanRows 435).J/2-(generalMeanRows 435).error (generalMeanGrid j.val)+
      (generalMeanRows 435).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 435).c)).2-
      (generalMeanRows 435).J/2-(generalMeanRows 435).error 4 := by
  have he : (generalMeanRows 435).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 435) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 435)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0435

/-! Kernel-checked entropy margins for general spectral rectangle 436. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0436
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5060940177, 4891798494, 4730232495, 4575806258, 4428114831, 4286781525, 4151455500, 4021809611, 3897538462, 3778356664, 3663997257, 3554210287, 3448761512, 3347431226, 3250013190, 3156313657, 3066150482, 2979352299, 2895757780, 2815214942, 2737580518, 2662719373, 2590503966, 2520813856, 2453535243, 2388560541, 2325787992, 2265121291, 2206469258, 2149745515, 2094868202, 2041759695, 1990346362, 1940558318, 1892329212, 1845596016, 1800298836, 1756380727, 1713787532, 1672467718, 1632372234, 1593454367, 1555669617, 1518975575, 1483331806, 1448699745, 1415042594, 1382325230, 1350514112, 1319577203, 1289483887, 1260204894, 1231712236, 1203979135, 1176979963, 1150690187, 1125086308, 1100145813, 1075847126, 1052169558, 1029093268, 1006599219, 984669137, 963285480, 942431396, 922090697, 902247820, 882887804, 863996259, 845559341, 827563723, 809996577, 792845547, 776098728, 759744649, 743772251, 728170866, 712930208, 698040348, 683491703, 669275018, 655381357, 641802084, 628528854, 615553599, 602868517, 590466061, 578338929, 566480054, 554882593, 543539920, 532445618, 521593467, 510977440, 500591695, 490430566, 480488558, 470760339, 461240735, 451924727, 442807438, 433884133, 425150216, 416601218, 408232797, 400040736, 392020930, 384169393, 376482244, 368955711, 361586121, 354369903, 347303578, 340383762, 333607158, 326970557, 320470831, 314104936, 307869904, 301762842, 295780932]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 436).prefactor = (2344808472719459/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 436).cutoff/(generalMeanRows 436).c)).2 =
    (49763573768177/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 436).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 436).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 436).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 436

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 436).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 436).criticalRate j.val*(generalMeanRows 436).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 436).c*(generalMeanRows 436).criticalPoint j.val)).2-
      (generalMeanRows 436).J/2-(generalMeanRows 436).error (generalMeanGrid j.val)+
      (generalMeanRows 436).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 436).c)).2-
      (generalMeanRows 436).J/2-(generalMeanRows 436).error 4 := by
  have he : (generalMeanRows 436).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 436) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 436)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0436

/-! Kernel-checked entropy margins for general spectral rectangle 437. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0437
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5216831238, 5047577936, 4885866946, 4731262349, 4583359301, 4441781310, 4306177819, 4176222038, 4051608995, 3932053782, 3817289974, 3707068197, 3601154829, 3499330820, 3401390618, 3307141188, 3216401118, 3128999794, 3044776655, 2963580497, 2885268838, 2809707336, 2736769248, 2666334929, 2598291378, 2532531805, 2468955241, 2407466169, 2347974188, 2290393693, 2234643585, 2180646995, 2128331031, 2077626542, 2028467896, 1980792770, 1934541963, 1889659214, 1846091029, 1803786529, 1762697301, 1722777255, 1683982500, 1646271222, 1609603565, 1573941529, 1539248865, 1505490985, 1472634870, 1440648988, 1409503213, 1379168755, 1349618087, 1320824879, 1292763939, 1265411155, 1238743436, 1212738664, 1187375642, 1162634051, 1138494407, 1114938014, 1091946932, 1069503937, 1047592486, 1026196685, 1005301258, 984891520, 964953342, 945473133, 926437812, 907834782, 889651910, 871877507, 854500305, 837509441, 820894437, 804645182, 788751918, 773205224, 757996002, 743115460, 728555103, 714306717, 700362361, 686714349, 673355248, 660277860, 647475218, 634940572, 622667385, 610649319, 598880232, 587354169, 576065351, 565008175, 554177202, 543567151, 533172896, 522989459, 513012003, 503235828, 493656365, 484269175, 475069938, 466054456, 457218642, 448558521, 440070222, 431749979, 423594125, 415599088, 407761388, 400077635, 392544528, 385158845, 377917450, 370817283, 363855359, 357028770, 350334676]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 437).prefactor = (1171816620114583/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 437).cutoff/(generalMeanRows 437).c)).2 =
    (8329282455607/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 437).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 437).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 437).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 437

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 437).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 437).criticalRate j.val*(generalMeanRows 437).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 437).c*(generalMeanRows 437).criticalPoint j.val)).2-
      (generalMeanRows 437).J/2-(generalMeanRows 437).error (generalMeanGrid j.val)+
      (generalMeanRows 437).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 437).c)).2-
      (generalMeanRows 437).J/2-(generalMeanRows 437).error 4 := by
  have he : (generalMeanRows 437).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 437) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 437)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0437

/-! Kernel-checked entropy margins for general spectral rectangle 438. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0438
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5234450315, 5064625385, 4902368239, 4747241489, 4598838920, 4456782770, 4320721298, 4190326611, 4065292706, 3945333713, 3830182307, 3719588272, 3613317198, 3511149293, 3412878313, 3318310569, 3227264037, 3139567529, 3055059939, 2973589552, 2895013407, 2819196708, 2746012282, 2675340082, 2607066723, 2541085057, 2477293772, 2415597030, 2355904124, 2298129160, 2242190764, 2188011808, 2135519155, 2084643419, 2035318746, 1987482605, 1941075593, 1896041259, 1852325929, 1809878552, 1768650550, 1728595680, 1689669903, 1651831260, 1615039764, 1579257284, 1544447450, 1510575558, 1477608477, 1445514567, 1414263602, 1383826694, 1354176222, 1325285770, 1297130059, 1269684895, 1242927109, 1216834509, 1191385827, 1166560676, 1142339503, 1118703552, 1095634822, 1073116028, 1051130575, 1029662512, 1008696515, 988217845, 968212329, 948666329, 929566719, 910900860, 892656578, 874822144, 857386254, 840338006, 823666887, 807362752, 791415811, 775816611, 760556021, 745625223, 731015690, 716719183, 702727731, 689033625, 675629406, 662507851, 649661970, 637084990, 624770352, 612711697, 600902862, 589337870, 578010927, 566916407, 556048853, 545402969, 534973609, 524755779, 514744625, 504935432, 495323617, 485904722, 476674417, 467628486, 458762831, 450073461, 441556494, 433208151, 425024752, 417002712, 409138542, 401428839, 393870289, 386459663, 379193811, 372069664, 365084227, 358234582, 351517879]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 438).prefactor = (2351548515308631/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 438).cutoff/(generalMeanRows 438).c)).2 =
    (8329282455607/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 438).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 438).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 438).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 438

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 438).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 438).criticalRate j.val*(generalMeanRows 438).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 438).c*(generalMeanRows 438).criticalPoint j.val)).2-
      (generalMeanRows 438).J/2-(generalMeanRows 438).error (generalMeanGrid j.val)+
      (generalMeanRows 438).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 438).c)).2-
      (generalMeanRows 438).J/2-(generalMeanRows 438).error 4 := by
  have he : (generalMeanRows 438).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 438) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 438)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0438

/-! Kernel-checked entropy margins for general spectral rectangle 439. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0439
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5078171300, 4908453736, 4746337648, 4591385632, 4443191356, 4301376848, 4165590076, 4035502777, 3910808519, 3791220939, 3676472170, 3566311405, 3460503606, 3358828318, 3261078600, 3167060046, 3076589889, 2989496182, 2905617046, 2824799982, 2746901235, 2671785208, 2599323927, 2529396541, 2461888862, 2396692940, 2333706666, 2272833412, 2213981684, 2157064814, 2102000658, 2048711331, 1997122949, 1947165391, 1898772078, 1851879768, 1806428363, 1762360725, 1719622511, 1678162015, 1637930016, 1598879645, 1560966249, 1524147273, 1488382147, 1453632173, 1419860429, 1387031671, 1355112245, 1324070004, 1293874228, 1264495549, 1235905881, 1208078356, 1180987259, 1154607974, 1128916920, 1103891510, 1079510092, 1055751909, 1032597050, 1010026415, 988021667, 966565205, 945640119, 925230164, 905319728, 885893796, 866937931, 848438240, 830381352, 812754395, 795544970, 778741133, 762331373, 746304593, 730650090, 715357542, 700416986, 685818806, 671553717, 657612752, 643987245, 630668824, 617649391, 604921120, 592476437, 580308016, 568408764, 556771817, 545390526, 534258450, 523369351, 512717179, 502296074, 492100349, 482124490, 472363149, 462811135, 453463408, 444315076, 435361391, 426597737, 418019631, 409622719, 401402765, 393355655, 385477385, 377764064, 370211904, 362817223, 355576436, 348486052, 341542676, 334742999, 328083802, 321561947, 315174378, 308918117, 302790262, 296787986]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 439).prefactor = (4705583813974087/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 439).cutoff/(generalMeanRows 439).c)).2 =
    (49763573768177/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 439).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 439).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 439).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 439

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 439).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 439).criticalRate j.val*(generalMeanRows 439).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 439).c*(generalMeanRows 439).criticalPoint j.val)).2-
      (generalMeanRows 439).J/2-(generalMeanRows 439).error (generalMeanGrid j.val)+
      (generalMeanRows 439).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 439).c)).2-
      (generalMeanRows 439).J/2-(generalMeanRows 439).error 4 := by
  have he : (generalMeanRows 439).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 439) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 439)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0439

/-! Kernel-checked entropy margins for general spectral rectangle 440. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0440
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5095461090, 4925165684, 4762497635, 4607018050, 4458319213, 4316021865, 4179772775, 4049242565, 3924123757, 3804129014, 3688989556, 3578453724, 3472285678, 3370264213, 3272181684, 3177843023, 3087064840, 2999674602, 2915509881, 2834417657, 2756253685, 2680881909, 2608173917, 2538008447, 2470270923, 2404853026, 2341652302, 2280571791, 2221519689, 2164409032, 2109157397, 2055686635, 2003922609, 1953794958, 1905236879, 1858184914, 1812578759, 1768361083, 1725477358, 1683875700, 1643506722, 1604323395, 1566280914, 1529336580, 1493449683, 1458581395, 1424694667, 1391754136, 1359726033, 1328578102, 1298279518, 1268800812, 1240113804, 1212191533, 1185008199, 1158539099, 1132760575, 1107649960, 1083185530, 1059346457, 1036112762, 1013465280, 991385612, 969856096, 948859766, 928380321, 908402095, 888910024, 869889619, 851326941, 833208575, 815521602, 798253584, 781392534, 764926904, 748845556, 733137755, 717793139, 702801715, 688153832, 673840175, 659851744, 646179847, 632816079, 619752319, 606980712, 594493658, 582283806, 570344041, 558667473, 547247432, 536077455, 525151281, 514462842, 504006255, 493775816, 483765993, 473971417, 464386880, 455007327, 445827848, 436843678, 428050186, 419442874, 411017373, 402769432, 394694924, 386789831, 379050247, 371472375, 364052517, 356787077, 349672552, 342705536, 335882708, 329200838, 322656778, 316247461, 309969899, 303821181, 297798468]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 440).prefactor = (4721605045348227/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 440).cutoff/(generalMeanRows 440).c)).2 =
    (49763573768177/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 440).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 440).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 440).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 440

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 440).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 440).criticalRate j.val*(generalMeanRows 440).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 440).c*(generalMeanRows 440).criticalPoint j.val)).2-
      (generalMeanRows 440).J/2-(generalMeanRows 440).error (generalMeanGrid j.val)+
      (generalMeanRows 440).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 440).c)).2-
      (generalMeanRows 440).J/2-(generalMeanRows 440).error 4 := by
  have he : (generalMeanRows 440).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 440) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 440)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0440

/-! Kernel-checked entropy margins for general spectral rectangle 441. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0441
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5314773506, 5142773854, 4978480202, 4821444412, 4671250387, 4527511272, 4389866955, 4257981832, 4131542797, 4010257429, 3893852368, 3782071825, 3674676252, 3571441116, 3472155796, 3376622563, 3284655665, 3196080469, 3110732694, 3028457691, 2949109790, 2872551694, 2798653926, 2727294308, 2658357492, 2591734516, 2527322401, 2465023765, 2404746482, 2346403350, 2289911791, 2235193566, 2182174516, 2130784318, 2080956253, 2032626996, 1985736415, 1940227390, 1896045634, 1853139533, 1811459992, 1770960298, 1731595979, 1693324684, 1656106065, 1619901663, 1584674809, 1550390528, 1517015441, 1484517685, 1452866830, 1422033804, 1391990822, 1362711317, 1334169876, 1306342184, 1279204965, 1252735928, 1226913722, 1201717880, 1177128785, 1153127619, 1129696329, 1106817586, 1084474752, 1062651846, 1041333510, 1020504984, 1000152072, 980261118, 960818982, 941813014, 923231031, 905061298, 887292504, 869913746, 852914507, 836284644, 820014365, 804094221, 788515083, 773268133, 758344850, 743736997, 729436608, 715435978, 701727650, 688304407, 675159263, 662285447, 649676405, 637325780, 625227412, 613375328, 601763734, 590387008, 579239693, 568316492, 557612263, 547122010, 536840879, 526764152, 516887246, 507205702, 497715184, 488411476, 479290474, 470348184, 461580719, 452984295, 444555226, 436289921, 428184884, 420236705, 412442062, 404797719, 397300517, 389947377, 382735297, 375661347, 368722669]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 441).prefactor = (955968400435177/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 441).cutoff/(generalMeanRows 441).c)).2 =
    (424856363912193/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 441).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 441).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 441).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 441

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 441).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 441).criticalRate j.val*(generalMeanRows 441).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 441).c*(generalMeanRows 441).criticalPoint j.val)).2-
      (generalMeanRows 441).J/2-(generalMeanRows 441).error (generalMeanGrid j.val)+
      (generalMeanRows 441).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 441).c)).2-
      (generalMeanRows 441).J/2-(generalMeanRows 441).error 4 := by
  have he : (generalMeanRows 441).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 441) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 441)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0441

/-! Kernel-checked entropy margins for general spectral rectangle 442. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0442
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5444665380, 5271204224, 5105490572, 4947073288, 4795533522, 4650481887, 4511555944, 4378417946, 4250752815, 4128266315, 4010683411, 3897746774, 3789215434, 3684863551, 3584479296, 3487863829, 3394830374, 3305203355, 3218817622, 3135517727, 3055157262, 2977598257, 2902710608, 2830371570, 2760465267, 2692882258, 2627519119, 2564278066, 2503066603, 2443797189, 2386386937, 2330757327, 2276833944, 2224546230, 2173827255, 2124613503, 2076844668, 2030463473, 1985415490, 1941648979, 1899114733, 1857765935, 1817558024, 1778448570, 1740397153, 1703365255, 1667316152, 1632214821, 1598027844, 1564723324, 1532270803, 1500641185, 1469806664, 1439740659, 1410417746, 1381813600, 1353904939, 1326669471, 1300085840, 1274133584, 1248793086, 1224045532, 1199872875, 1176257793, 1153183653, 1130634482, 1108594931, 1087050248, 1065986245, 1045389275, 1025246208, 1005544400, 986271679, 967416315, 948967007, 930912857, 913243357, 895948368, 879018105, 862443122, 846214296, 830322810, 814760148, 799518073, 784588620, 769964084, 755637009, 741600175, 727846592, 714369489, 701162305, 688218679, 675532445, 663097624, 650908413, 638959182, 627244464, 615758954, 604497497, 593455084, 582626851, 572008066, 561594130, 551380571, 541363037, 531537295, 521899223, 512444812, 503170154, 494071446, 485144982, 476387152, 467794438, 459363408, 451090720, 442973111, 435007403, 427190491, 419519349, 411991022, 404602627]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 442).prefactor = (4811972284467731/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 442).cutoff/(generalMeanRows 442).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 442).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 442).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 442).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 442

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 442).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 442).criticalRate j.val*(generalMeanRows 442).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 442).c*(generalMeanRows 442).criticalPoint j.val)).2-
      (generalMeanRows 442).J/2-(generalMeanRows 442).error (generalMeanGrid j.val)+
      (generalMeanRows 442).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 442).c)).2-
      (generalMeanRows 442).J/2-(generalMeanRows 442).error 4 := by
  have he : (generalMeanRows 442).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 442) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 442)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0442

/-! Kernel-checked entropy margins for general spectral rectangle 443. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0443
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5121739184, 4948384463, 4782847702, 4624677828, 4473455833, 4328791975, 4190323284, 4057711321, 3930640174, 3808814647, 3691958629, 3579813621, 3472137390, 3368702760, 3269296500, 3173718311, 3081779909, 2993304171, 2908124368, 2826083444, 2747033368, 2670834527, 2597355169, 2526470892, 2458064167, 2392023900, 2328245022, 2266628113, 2207079054, 2149508697, 2093832562, 2039970560, 1987846725, 1937388971, 1888528866, 1841201415, 1795344861, 1750900503, 1707812516, 1666027792, 1625495785, 1586168372, 1547999712, 1510946125, 1474965974, 1440019553, 1406068980, 1373078105, 1341012414, 1309838941, 1279526193, 1250044065, 1221363774, 1193457789, 1166299765, 1139864487, 1114127808, 1089066597, 1064658692, 1040882844, 1017718681, 995146658, 973148020, 951704763, 930799599, 910415920, 890537767, 871149798, 852237261, 833785966, 815782257, 798212991, 781065512, 764327628, 747987595, 732034090, 716456199, 701243395, 686385521, 671872777, 657695699, 643845153, 630312313, 617088650, 604165924, 591536166, 579191669, 567124981, 555328887, 543796406, 532520779, 521495461, 510714109, 500170582, 489858923, 479773361, 469908297, 460258304, 450818113, 441582613, 432546844, 423705989, 415055371, 406590447, 398306804, 390200153, 382266328, 374501276, 366901058, 359461842, 352179902, 345051614, 338073448, 331241971, 324553842, 318005807, 311594697, 305317426, 299170988, 293152455, 287258974]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 443).prefactor = (602207936767149/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 443).cutoff/(generalMeanRows 443).c)).2 =
    (395518068812987/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 443).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 443).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 443).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 443

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 443).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 443).criticalRate j.val*(generalMeanRows 443).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 443).c*(generalMeanRows 443).criticalPoint j.val)).2-
      (generalMeanRows 443).J/2-(generalMeanRows 443).error (generalMeanGrid j.val)+
      (generalMeanRows 443).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 443).c)).2-
      (generalMeanRows 443).J/2-(generalMeanRows 443).error 4 := by
  have he : (generalMeanRows 443).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 443) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 443)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0443

/-! Kernel-checked entropy margins for general spectral rectangle 444. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0444
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5245601884, 5070633277, 4903527028, 4743829097, 4591117751, 4445000742, 4305112795, 4171113345, 4042684524, 3919529332, 3801369995, 3687946476, 3579015129, 3474347469, 3373729055, 3276958476, 3183846416, 3094214803, 3007896026, 2924732221, 2844574604, 2767282872, 2692724632, 2620774894, 2551315582, 2484235098, 2419427910, 2356794170, 2296239363, 2237673975, 2181013193, 2126176615, 2073087991, 2021674972, 1971868883, 1923604506, 1876819878, 1831456109, 1787457201, 1744769884, 1703343467, 1663129689, 1624082585, 1586158361, 1549315274, 1513513518, 1478715126, 1444883862, 1411985137, 1379985916, 1348854638, 1318561140, 1289076584, 1260373385, 1232425152, 1205206624, 1178693611, 1152862946, 1127692426, 1103160769, 1079247570, 1055933252, 1033199030, 1011026871, 989399458, 968300157, 947712983, 927622567, 908014132, 888873463, 870186880, 851941215, 834123786, 816722379, 799725222, 783120971, 766898686, 751047813, 735558171, 720419933, 705623612, 691160044, 677020377, 663196056, 649678811, 636460647, 623533827, 610890870, 598524531, 586427800, 574593886, 563016212, 551688407, 540604293, 529757884, 519143374, 508755132, 498587695, 488635761, 478894184, 469357968, 460022260, 450882347, 441933650, 433171719, 424592229, 416190973, 407963862, 399906918, 392016272, 384288159, 376718913, 369304967, 362042849, 354929176, 347960655, 341134076, 334446314, 327894322, 321475130, 315185845]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 444).prefactor = (2425285975595011/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 444).cutoff/(generalMeanRows 444).c)).2 =
    (100817511404327/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 444).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 444).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 444).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 444

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 444).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 444).criticalRate j.val*(generalMeanRows 444).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 444).c*(generalMeanRows 444).criticalPoint j.val)).2-
      (generalMeanRows 444).J/2-(generalMeanRows 444).error (generalMeanGrid j.val)+
      (generalMeanRows 444).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 444).c)).2-
      (generalMeanRows 444).J/2-(generalMeanRows 444).error 4 := by
  have he : (generalMeanRows 444).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 444) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 444)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0444

/-! Kernel-checked entropy margins for general spectral rectangle 445. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0445
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5481264631, 5306637462, 5139809876, 4980327706, 4827769284, 4681742606, 4541882797, 4407849840, 4279326539, 4156016680, 4037643379, 3923947578, 3814686687, 3709633346, 3608574304, 3511309385, 3417650555, 3327421060, 3240454639, 3156594798, 3075694147, 2997613787, 2922222741, 2849397437, 2779021221, 2710983916, 2645181404, 2581515242, 2519892313, 2460224488, 2402428322, 2346424767, 2292138909, 2239499715, 2188439806, 2138895236, 2090805298, 2044112327, 1998761530, 1954700819, 1911880655, 1870253909, 1829775719, 1790403370, 1752096170, 1714815341, 1678523915, 1643186632, 1608769849, 1575241455, 1542570786, 1510728553, 1479686762, 1449418651, 1419898628, 1391102204, 1363005940, 1335587394, 1308825067, 1282698359, 1257187521, 1232273614, 1207938467, 1184164643, 1160935398, 1138234651, 1116046949, 1094357442, 1073151845, 1052416422, 1032137952, 1012303708, 992901435, 973919325, 955345999, 937170489, 919382214, 901970967, 884926899, 868240498, 851902581, 835904272, 820236997, 804892464, 789862655, 775139813, 760716430, 746585240, 732739205, 719171508, 705875545, 692844911, 680073401, 667554992, 655283845, 643254290, 631460826, 619898110, 608560952, 597444312, 586543291, 575853126, 565369188, 555086973, 545002101, 535110309, 525407450, 515889485, 506552483, 497392613, 488406145, 479589445, 470938970, 462451267, 454122969, 445950794, 437931539, 430062082, 422339374, 414760442, 407322381]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 445).prefactor = (2422159273878189/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 445).cutoff/(generalMeanRows 445).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 445).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 445).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 445).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 445

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 445).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 445).criticalRate j.val*(generalMeanRows 445).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 445).c*(generalMeanRows 445).criticalPoint j.val)).2-
      (generalMeanRows 445).J/2-(generalMeanRows 445).error (generalMeanGrid j.val)+
      (generalMeanRows 445).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 445).c)).2-
      (generalMeanRows 445).J/2-(generalMeanRows 445).error 4 := by
  have he : (generalMeanRows 445).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 445) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 445)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0445

/-! Kernel-checked entropy margins for general spectral rectangle 446. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0446
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5151065399, 4964178580, 4785857481, 4615612474, 4452988412, 4297561627, 4148937251, 4006746809, 3870646073, 3740313123, 3615446594, 3495764098, 3381000786, 3270908050, 3165252331, 3063814039, 2966386565, 2872775370, 2782797160, 2696279121, 2613058216, 2532980538, 2455900716, 2381681361, 2310192561, 2241311402, 2174921539, 2110912786, 2049180738, 1989626425, 1932155982, 1876680349, 1823114986, 1771379607, 1721397941, 1673097492, 1626409331, 1581267894, 1537610790, 1495378626, 1454514843, 1414965561, 1376679430, 1339607496, 1303703072, 1268921619, 1235220628, 1202559517, 1170899530, 1140203642, 1110436469, 1081564184, 1053554440, 1026376293, 1000000131, 974397612, 949541594, 925406083, 901966171, 879197986, 857078643, 835586195, 814699585, 794398610, 774663876, 755476764, 736819387, 718674565, 701025786, 683857176, 667153473, 650899998, 635082627, 619687767, 604702336, 590113734, 575909826, 562078923, 548609759, 535491473, 522713597, 510266032, 498139036, 486323211, 474809484, 463589098, 452653594, 441994806, 431604841, 421476074, 411601134, 401972894, 392584465, 383429181, 374500595, 365792468, 357298760, 349013628, 340931409, 333046624, 325353961, 317848277, 310524587, 303378059, 296404008, 289597893, 282955310, 276471987, 270143779, 263966666, 257936743, 252050223, 246303430, 240692791, 235214840, 229866209, 224643626, 219543913, 214563980, 209700827, 204951535]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 446).prefactor = (2589379920427433/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 446).cutoff/(generalMeanRows 446).c)).2 =
    (347341734459821/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 446).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 446).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 446).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 446

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 446).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 446).criticalRate j.val*(generalMeanRows 446).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 446).c*(generalMeanRows 446).criticalPoint j.val)).2-
      (generalMeanRows 446).J/2-(generalMeanRows 446).error (generalMeanGrid j.val)+
      (generalMeanRows 446).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 446).c)).2-
      (generalMeanRows 446).J/2-(generalMeanRows 446).error 4 := by
  have he : (generalMeanRows 446).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 446) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 446)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0446

/-! Kernel-checked entropy margins for general spectral rectangle 447. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0447
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5372948650, 5196389674, 5027737214, 4866534217, 4712356178, 4564808304, 4423522973, 4288157464, 4158391920, 4033927507, 3914484761, 3799802088, 3689634401, 3583751889, 3481938887, 3383992852, 3289723426, 3198951571, 3111508790, 3027236396, 2945984849, 2867613147, 2791988253, 2718984582, 2648483510, 2580372935, 2514546859, 2450905006, 2389352465, 2329799362, 2272160547, 2216355313, 2162307128, 2109943385, 2059195170, 2009997046, 1962286854, 1916005519, 1871096875, 1827507501, 1785186564, 1744085676, 1704158756, 1665361903, 1627653276, 1590992984, 1555342976, 1520666944, 1486930233, 1454099745, 1422143867, 1391032385, 1360736413, 1331228327, 1302481696, 1274471226, 1247172695, 1220562906, 1194619630, 1169321562, 1144648271, 1120580160, 1097098425, 1074185014, 1051822592, 1029994508, 1008684761, 987877967, 967559333, 947714629, 928330161, 909392745, 890889686, 872808754, 855138163, 837866553, 820982968, 804476840, 788337970, 772556517, 757122973, 742028160, 727263206, 712819538, 698688868, 684863179, 671334715, 658095974, 645139689, 632458828, 620046578, 607896338, 596001712, 584356500, 572954689, 561790447, 550858117, 540152209, 529667393, 519398496, 509340493, 499488501, 489837778, 480383715, 471121830, 462047768, 453157290, 444446275, 435910712, 427546700, 419350438, 411318229, 403446471, 395731658, 388170371, 380759282, 373495146, 366374802, 359395167, 352553235, 345846076]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 447).prefactor = (4883705199066643/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 447).cutoff/(generalMeanRows 447).c)).2 =
    (411082585354099/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 447).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 447).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 447).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 447

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 447).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 447).criticalRate j.val*(generalMeanRows 447).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 447).c*(generalMeanRows 447).criticalPoint j.val)).2-
      (generalMeanRows 447).J/2-(generalMeanRows 447).error (generalMeanGrid j.val)+
      (generalMeanRows 447).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 447).c)).2-
      (generalMeanRows 447).J/2-(generalMeanRows 447).error 4 := by
  have he : (generalMeanRows 447).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 447) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 447)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0447

/-! Kernel-checked entropy margins for general spectral rectangle 448. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0448
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5503886046, 5325762790, 5155589995, 4992907540, 4837288104, 4688334303, 4545676131, 4408968671, 4277890045, 4152139554, 4031436017, 3915516254, 3804133717, 3697057247, 3594069934, 3494968088, 3399560291, 3307666529, 3219117404, 3133753397, 3051424204, 2971988113, 2895311439, 2821267996, 2749738608, 2680610666, 2613777704, 2549139016, 2486599297, 2426068309, 2367460571, 2310695072, 2255695000, 2202387491, 2150703399, 2100577075, 2051946164, 2004751412, 1958936495, 1914447843, 1871234491, 1829247930, 1788441970, 1748772611, 1710197925, 1672677938, 1636174529, 1600651326, 1566073614, 1532408247, 1499623564, 1467689310, 1436576564, 1406257671, 1376706171, 1347896744, 1319805148, 1292408167, 1265683555, 1239609993, 1214167037, 1189335079, 1165095306, 1141429657, 1118320791, 1095752048, 1073707422, 1052171525, 1031129558, 1010567285, 990471009, 970827540, 951624179, 932848690, 914489284, 896534594, 878973658, 861795902, 844991122, 828549467, 812461424, 796717805, 781309729, 766228614, 751466161, 737014343, 722865392, 709011793, 695446267, 682161767, 669151467, 656408749, 643927203, 631700610, 619722941, 607988345, 596491148, 585225839, 574187068, 563369641, 552768511, 542378773, 532195663, 522214548, 512430921, 502840403, 493438729, 484221753, 475185438, 466325854, 457639175, 449121674, 440769722, 432579782, 424548407, 416672240, 408948004, 401372509, 393942639, 386655359, 379507704]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 448).prefactor = (491706477326641/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 448).cutoff/(generalMeanRows 448).c)).2 =
    (209478320892503/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 448).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 448).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 448).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 448

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 448).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 448).criticalRate j.val*(generalMeanRows 448).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 448).c*(generalMeanRows 448).criticalPoint j.val)).2-
      (generalMeanRows 448).J/2-(generalMeanRows 448).error (generalMeanGrid j.val)+
      (generalMeanRows 448).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 448).c)).2-
      (generalMeanRows 448).J/2-(generalMeanRows 448).error 4 := by
  have he : (generalMeanRows 448).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 448) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 448)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0448

/-! Kernel-checked entropy margins for general spectral rectangle 449. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0449
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5323247767, 5153184824, 4990689894, 4835323991, 4686679495, 4544377409, 4408064915, 4277413182, 4152115401, 4031885013, 3916454110, 3805571990, 3699003843, 3596529561, 3497942651, 3403049243, 3311667190, 3223625233, 3138762244, 3056926528, 2977975183, 2901773504, 2828194442, 2757118101, 2688431269, 2622026991, 2557804171, 2495667198, 2435525608, 2377293762, 2320890550, 2266239117, 2213266604, 2161903910, 2112085469, 2063749041, 2016835516, 1971288737, 1927055324, 1884084518, 1842328034, 1801739917, 1762276414, 1723895853, 1686558524, 1650226573, 1614863903, 1580436075, 1546910221, 1514254960, 1482440317, 1451437650, 1421219580, 1391759925, 1363033637, 1335016745, 1307686299, 1281020318, 1254997740, 1229598378, 1204802875, 1180592663, 1156949922, 1133857547, 1111299110, 1089258831, 1067721542, 1046672660, 1026098162, 1005984552, 986318843, 967088531, 948281569, 929886352, 911891694, 894286808, 877061289, 860205097, 843708542, 827562268, 811757236, 796284712, 781136256, 766303707, 751779171, 737555010, 723623832, 709978482, 696612029, 683517760, 670689169, 658119949, 645803987, 633735351, 621908289, 610317216, 598956713, 587821516, 576906515, 566206743, 555717374, 545433719, 535351216, 525465430, 515772048, 506266871, 496945815, 487804903, 478840264, 470048127, 461424820, 452966765, 444670476, 436532553, 428549685, 420718641, 413036271, 405499503, 398105338, 390850852, 383733190]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 449).prefactor = (58954414151269/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 449).cutoff/(generalMeanRows 449).c)).2 =
    (106799093155119/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 449).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 449).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 449).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 449

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 449).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 449).criticalRate j.val*(generalMeanRows 449).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 449).c*(generalMeanRows 449).criticalPoint j.val)).2-
      (generalMeanRows 449).J/2-(generalMeanRows 449).error (generalMeanGrid j.val)+
      (generalMeanRows 449).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 449).c)).2-
      (generalMeanRows 449).J/2-(generalMeanRows 449).error 4 := by
  have he : (generalMeanRows 449).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 449) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 449)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0449

/-! Kernel-checked entropy margins for general spectral rectangle 450. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0450
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5061824339, 4885670308, 4717490966, 4556828984, 4403259389, 4256386748, 4115842645, 3981283428, 3852388185, 3728856922, 3610408917, 3496781236, 3387727381, 3283016068, 3182430105, 3085765381, 2992829929, 2903443080, 2817434677, 2734644362, 2654920910, 2578121627, 2504111789, 2432764118, 2363958312, 2297580596, 2233523313, 2171684544, 2111967754, 2054281462, 1998538939, 1944657918, 1892560336, 1842172077, 1793422753, 1746245477, 1700576669, 1656355868, 1613525549, 1572030966, 1531819991, 1492842975, 1455052605, 1418403784, 1382853506, 1348360745, 1314886350, 1282392945, 1250844835, 1220207919, 1190449607, 1161538740, 1133445519, 1106141437, 1079599208, 1053792711, 1028696928, 1004287893, 980542636, 957439136, 934956276, 913073796, 891772255, 871032990, 850838079, 831170307, 812013130, 793350649, 775167574, 757449202, 740181383, 723350502, 706943451, 690947607, 675350808, 660141337, 645307902, 630839611, 616725964, 602956828, 589522426, 576413322, 563620403, 551134868, 538948214, 527052228, 515438965, 504100750, 493030155, 482219997, 471663327, 461353417, 451283754, 441448034, 431840147, 422454177, 413284390, 404325230, 395571307, 387017398, 378658437, 370489508, 362505841, 354702808, 347075917, 339620803, 332333232, 325209089, 318244377, 311435212, 304777819, 298268530, 291903779, 285680097, 279594111, 273642542, 267822198, 262129974, 256562849, 251117880, 245792206]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 450).prefactor = (4890546907568019/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 450).cutoff/(generalMeanRows 450).c)).2 =
    (74865395776473/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 450).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 450).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 450).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 450

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 450).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 450).criticalRate j.val*(generalMeanRows 450).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 450).c*(generalMeanRows 450).criticalPoint j.val)).2-
      (generalMeanRows 450).J/2-(generalMeanRows 450).error (generalMeanGrid j.val)+
      (generalMeanRows 450).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 450).c)).2-
      (generalMeanRows 450).J/2-(generalMeanRows 450).error 4 := by
  have he : (generalMeanRows 450).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 450) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 450)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0450

/-! Kernel-checked entropy margins for general spectral rectangle 451. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0451
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5044139452, 4873114288, 4709777463, 4553686940, 4404432057, 4261630787, 4124927290, 3993989731, 3868508313, 3748193510, 3632774470, 3521997571, 3415625113, 3313434127, 3215215292, 3120771946, 3029919186, 2942483036, 2858299693, 2777214828, 2699082947, 2623766800, 2551136838, 2481070711, 2413452801, 2348173796, 2285130290, 2224224411, 2165363485, 2108459709, 2053429863, 2000195027, 1948680331, 1898814708, 1850530676, 1803764130, 1758454141, 1714542781, 1671974946, 1630698203, 1590662635, 1551820703, 1514127115, 1477538703, 1442014306, 1407514663, 1374002309, 1341441481, 1309798028, 1279039324, 1249134189, 1220052815, 1191766695, 1164248555, 1137472291, 1111412912, 1086046481, 1061350065, 1037301684, 1013880262, 991065586, 968838263, 947179678, 926071959, 905497941, 885441132, 865885681, 846816348, 828218477, 810077967, 792381247, 775115252, 758267402, 741825575, 725778093, 710113696, 694821529, 679891121, 665312368, 651075521, 637171164, 623590206, 610323866, 597363658, 584701378, 572329097, 560239144, 548424100, 536876785, 525590250, 514557767, 503772819, 493229095, 482920479, 472841044, 462985044, 453346906, 443921228, 434702767, 425686434, 416867294, 408240553, 399801557, 391545785, 383468846, 375566474, 367834522, 360268961, 352865871, 345621442, 338531969, 331593846, 324803565, 318157715, 311652972, 305286102, 299053957, 292953471, 286981657, 281135606, 275412485]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 451).prefactor = (4753811337606229/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 451).cutoff/(generalMeanRows 451).c)).2 =
    (78094993058069/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 451).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 451).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 451).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 451

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 451).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 451).criticalRate j.val*(generalMeanRows 451).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 451).c*(generalMeanRows 451).criticalPoint j.val)).2-
      (generalMeanRows 451).J/2-(generalMeanRows 451).error (generalMeanGrid j.val)+
      (generalMeanRows 451).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 451).c)).2-
      (generalMeanRows 451).J/2-(generalMeanRows 451).error 4 := by
  have he : (generalMeanRows 451).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 451) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 451)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0451

/-! Kernel-checked entropy margins for general spectral rectangle 452. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0452
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5165210930, 4992584414, 4827689664, 4670081777, 4519347458, 4375102255, 4236988104, 4104671115, 3977839602, 3856202297, 3739486739, 3627437824, 3519816483, 3416398485, 3316973341, 3221343314, 3129322502, 3040736013, 2955419193, 2873216928, 2793982999, 2717579487, 2643876223, 2572750285, 2504085527, 2437772150, 2373706294, 2311789675, 2251929232, 2194036808, 2138028855, 2083826152, 2031353547, 1980539718, 1931316946, 1883620905, 1837390464, 1792567509, 1749096765, 1706925637, 1666004064, 1626284370, 1587721140, 1550271090, 1513892951, 1478547364, 1444196774, 1410805332, 1378338809, 1346764505, 1316051175, 1286168946, 1257089252, 1228784765, 1201229328, 1174397903, 1148266506, 1122812161, 1098012847, 1073847449, 1050295718, 1027338222, 1004956315, 983132089, 961848348, 941088568, 920836868, 901077977, 881797209, 862980434, 844614052, 826684969, 809180575, 792088721, 775397699, 759096220, 743173400, 727618738, 712422101, 697573709, 683064118, 668884205, 655025158, 641478459, 628235874, 615289441, 602631457, 590254469, 578151265, 566314861, 554738495, 543415616, 532339878, 521505129, 510905406, 500534927, 490388083, 480459433, 470743697, 461235750, 451930617, 442823466, 433909603, 425184469, 416643634, 408282791, 400097753, 392084450, 384238923, 376557320, 369035894, 361671000, 354459088, 347396702, 340480480, 333707144, 327073504, 320576453, 314212959, 307980074, 301874919]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 452).prefactor = (598279663814163/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 452).cutoff/(generalMeanRows 452).c)).2 =
    (49763573768177/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 452).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 452).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 452).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 452

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 452).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 452).criticalRate j.val*(generalMeanRows 452).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 452).c*(generalMeanRows 452).criticalPoint j.val)).2-
      (generalMeanRows 452).J/2-(generalMeanRows 452).error (generalMeanGrid j.val)+
      (generalMeanRows 452).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 452).c)).2-
      (generalMeanRows 452).J/2-(generalMeanRows 452).error 4 := by
  have he : (generalMeanRows 452).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 452) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 452)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0452

/-! Kernel-checked entropy margins for general spectral rectangle 453. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0453
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5183407221, 5005519459, 4835653698, 4673349611, 4518179473, 4369745317, 4227676391, 4091626892, 3961273923, 3836315658, 3716469683, 3601471501, 3491073169, 3385042066, 3283159763, 3185221006, 3091032767, 3000413398, 2913191831, 2829206867, 2748306502, 2670347317, 2595193918, 2522718407, 2452799903, 2385324097, 2320182835, 2257273740, 2196499847, 2137769280, 2080994940, 2026094219, 1972988735, 1921604079, 1871869584, 1823718110, 1777085840, 1731912089, 1688139128, 1645712017, 1604578450, 1564688609, 1525995025, 1488452455, 1452017755, 1416649770, 1382309230, 1348958644, 1316562210, 1285085727, 1254496509, 1224763307, 1195856238, 1167746711, 1140407364, 1113812002, 1087935537, 1062753933, 1038244157, 1014384123, 991152655, 968529433, 946494960, 925030515, 904118124, 883740517, 863881099, 844523919, 825653638, 807255501, 789315310, 771819402, 754754619, 738108290, 721868207, 706022605, 690560143, 675469884, 660741278, 646364147, 632328667, 618625353, 605245045, 592178895, 579418353, 566955156, 554781315, 542889102, 531271045, 519919911, 508828702, 497990642, 487399169, 477047929, 466930765, 457041709, 447374980, 437924969, 428686239, 419653517, 410821685, 402185778, 393740975, 385482598, 377406104, 369507078, 361781235, 354224409, 346832552, 339601730, 332528117, 325607994, 318837743, 312213845, 305732878, 299391509, 293186497, 287114686, 281173003, 275358458, 269668137]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 453).prefactor = (615562454343137/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 453).cutoff/(generalMeanRows 453).c)).2 =
    (76392120747487/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 453).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 453).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 453).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 453

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 453).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 453).criticalRate j.val*(generalMeanRows 453).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 453).c*(generalMeanRows 453).criticalPoint j.val)).2-
      (generalMeanRows 453).J/2-(generalMeanRows 453).error (generalMeanGrid j.val)+
      (generalMeanRows 453).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 453).c)).2-
      (generalMeanRows 453).J/2-(generalMeanRows 453).error 4 := by
  have he : (generalMeanRows 453).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 453) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 453)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0453

/-! Kernel-checked entropy margins for general spectral rectangle 454. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0454
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5308399020, 5128796298, 4957262615, 4793334605, 4636581745, 4486603496, 4343026736, 4205503479, 4073708815, 3947339058, 3826110081, 3709755801, 3598026812, 3490689138, 3387523102, 3288322289, 3192892605, 3101051406, 3012626713, 2927456474, 2845387901, 2766276850, 2689987251, 2616390583, 2545365390, 2476796826, 2410576244, 2346600806, 2284773125, 2225000931, 2167196760, 2111277669, 2057164960, 2004783936, 1954063663, 1904936752, 1857339154, 1811209972, 1766491278, 1723127948, 1681067505, 1640259974, 1600657738, 1562215416, 1524889739, 1488639432, 1453425113, 1419209190, 1385955763, 1353630541, 1322200753, 1291635072, 1261903538, 1232977490, 1204829500, 1177433310, 1150763771, 1124796790, 1099509280, 1074879104, 1050885033, 1027506701, 1004724563, 982519855, 960874556, 939771355, 919193616, 899125346, 879551164, 860456278, 841826449, 823647976, 805907662, 788592798, 771691137, 755190877, 739080638, 723349445, 707986710, 692982216, 678326101, 664008842, 650021238, 636354405, 622999751, 609948975, 597194046, 584727198, 572540918, 560627931, 548981200, 537593905, 526459444, 515571421, 504923635, 494510077, 484324922, 474362519, 464617387, 455084208, 445757821, 436633215, 427705528, 418970034, 410422146, 402057404, 393871478, 385860155, 378019342, 370345058, 362833433, 355480700, 348283196, 341237355, 334339708, 327586876, 320975571, 314502590, 308164815, 301959207, 295882806]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 454).prefactor = (2479344039730723/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 454).cutoff/(generalMeanRows 454).c)).2 =
    (389652949360589/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 454).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 454).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 454).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 454

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 454).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 454).criticalRate j.val*(generalMeanRows 454).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 454).c*(generalMeanRows 454).criticalPoint j.val)).2-
      (generalMeanRows 454).J/2-(generalMeanRows 454).error (generalMeanGrid j.val)+
      (generalMeanRows 454).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 454).c)).2-
      (generalMeanRows 454).J/2-(generalMeanRows 454).error 4 := by
  have he : (generalMeanRows 454).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 454) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 454)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0454

/-! Kernel-checked entropy margins for general spectral rectangle 455. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0455
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5289655918, 5115449884, 4949018792, 4789914829, 4637722020, 4492053455, 4352548804, 4218872095, 4090709720, 3967768641, 3849774768, 3736471489, 3627618350, 3522989835, 3422374276, 3325572841, 3232398624, 3142675799, 3056238856, 2972931888, 2892607944, 2815128428, 2740362550, 2668186812, 2598484539, 2531145440, 2466065208, 2403145140, 2342291793, 2283416659, 2226435864, 2171269888, 2117843306, 2066084541, 2015925642, 1967302070, 1920152499, 1874418633, 1830045033, 1786978954, 1745170193, 1704570950, 1665135690, 1626821024, 1589585585, 1553389925, 1518196405, 1483969103, 1450673719, 1418277493, 1386749117, 1356058670, 1326177534, 1297078335, 1268734878, 1241122084, 1214215934, 1187993420, 1162432488, 1137511996, 1113211666, 1089512043, 1066394454, 1043840970, 1021834371, 1000358113, 979396293, 958933620, 938955389, 919447450, 900396183, 881788476, 863611698, 845853681, 828502697, 811547439, 794977001, 778780864, 762948872, 747471226, 732338458, 717541426, 703071293, 688919521, 675077850, 661538295, 648293129, 635334874, 622656292, 610250374, 598110330, 586229583, 574601758, 563220675, 552080344, 541174951, 530498859, 520046596, 509812852, 499792469, 489980441, 480371903, 470962130, 461746528, 452720634, 443880106, 435220724, 426738382, 418429086, 410288949, 402314188, 394501119, 386846159, 379345814, 371996684, 364795455, 357738898, 350823867, 344047296, 337406194, 330897646]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 455).prefactor = (301180278907599/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 455).cutoff/(generalMeanRows 455).c)).2 =
    (40580093576857/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 455).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 455).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 455).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 455

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 455).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 455).criticalRate j.val*(generalMeanRows 455).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 455).c*(generalMeanRows 455).criticalPoint j.val)).2-
      (generalMeanRows 455).J/2-(generalMeanRows 455).error (generalMeanGrid j.val)+
      (generalMeanRows 455).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 455).c)).2-
      (generalMeanRows 455).J/2-(generalMeanRows 455).error 4 := by
  have he : (generalMeanRows 455).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 455) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 455)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0455

/-! Kernel-checked entropy margins for general spectral rectangle 456. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0456
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5511484110, 5335395517, 5167114302, 5006189749, 4852203253, 4704765513, 4563514027, 4428110853, 4298240600, 4173608609, 4053939325, 3938974816, 3828473427, 3722208569, 3619967603, 3521550828, 3426770558, 3335450273, 3247423845, 3162534818, 3080635758, 3001587646, 2925259322, 2851526969, 2780273636, 2711388802, 2644767964, 2580312261, 2517928122, 2457526941, 2399024772, 2342342047, 2287403313, 2234136989, 2182475134, 2132353236, 2083710010, 2036487216, 1990629478, 1946084128, 1902801049, 1860732530, 1819833139, 1780059590, 1741370626, 1703726912, 1667090929, 1631426872, 1596700567, 1562879373, 1529932111, 1497828981, 1466541494, 1436042399, 1406305624, 1377306214, 1349020273, 1321424910, 1294498190, 1268219088, 1242567438, 1217523897, 1193069899, 1169187621, 1145859947, 1123070429, 1100803263, 1079043252, 1057775777, 1036986777, 1016662715, 996790556, 977357749, 958352196, 939762239, 921576637, 903784546, 886375504, 869339414, 852666525, 836347420, 820373001, 804734474, 789423338, 774431371, 759750618, 745373380, 731292208, 717499885, 703989422, 690754046, 677787194, 665082504, 652633803, 640435106, 628480605, 616764661, 605281802, 594026712, 582994228, 572179334, 561577154, 551182950, 540992112, 531000160, 521202731, 511595585, 502174592, 492935731, 483875090, 474988857, 466273317, 457724855, 449339943, 441115146, 433047113, 425132578, 417368356, 409751339, 402278495, 394946866]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 456).prefactor = (606469287788029/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 456).cutoff/(generalMeanRows 456).c)).2 =
    (84273090461937/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 456).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 456).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 456).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 456

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 456).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 456).criticalRate j.val*(generalMeanRows 456).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 456).c*(generalMeanRows 456).criticalPoint j.val)).2-
      (generalMeanRows 456).J/2-(generalMeanRows 456).error (generalMeanGrid j.val)+
      (generalMeanRows 456).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 456).c)).2-
      (generalMeanRows 456).J/2-(generalMeanRows 456).error 4 := by
  have he : (generalMeanRows 456).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 456) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 456)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0456

/-! Kernel-checked entropy margins for general spectral rectangle 457. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0457
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5275126768, 5086251574, 4905997476, 4733871553, 4569415631, 4412203245, 4261836948, 4117945884, 3980183623, 3848226207, 3721770386, 3600532021, 3484244645, 3372658146, 3265537568, 3162662025, 3063823703, 2968826942, 2877487408, 2789631313, 2705094719, 2623722875, 2545369626, 2469896851, 2397173953, 2327077383, 2259490198, 2194301655, 2131406828, 2070706259, 2012105627, 1955515443, 1900850766, 1848030935, 1796979321, 1747623099, 1699893028, 1653723246, 1609051085, 1565816891, 1523963859, 1483437871, 1444187359, 1406163157, 1369318379, 1333608297, 1298990221, 1265423398, 1232868908, 1201289568, 1170649845, 1140915768, 1112054852, 1084036019, 1056829531, 1030406921, 1004740928, 979805442, 955575444, 932026954, 909136979, 886883469, 865245268, 844202074, 823734398, 803823524, 784451476, 765600982, 747255439, 729398889, 712015982, 695091953, 678612593, 662564229, 646933694, 631708308, 616875856, 602424567, 588343097, 574620507, 561246250, 548210150, 535502389, 523113492, 511034309, 499256008, 487770057, 476568212, 465642507, 454985243, 444588975, 434446503, 424550865, 414895323, 405473356, 396278654, 387305106, 378546795, 369997990, 361653138, 353506860, 345553941, 337789325, 330208112, 322805548, 315577023, 308518063, 301624330, 294891609, 288315814, 281892973, 275619232, 269490847, 263504181, 257655703, 251941977, 246359669, 240905534, 235576420, 230369263, 225281080]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 457).prefactor = (5215951449869421/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 457).cutoff/(generalMeanRows 457).c)).2 =
    (355004607205391/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 457).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 457).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 457).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 457

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 457).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 457).criticalRate j.val*(generalMeanRows 457).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 457).c*(generalMeanRows 457).criticalPoint j.val)).2-
      (generalMeanRows 457).J/2-(generalMeanRows 457).error (generalMeanGrid j.val)+
      (generalMeanRows 457).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 457).c)).2-
      (generalMeanRows 457).J/2-(generalMeanRows 457).error 4 := by
  have he : (generalMeanRows 457).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 457) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 457)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0457

/-! Kernel-checked entropy margins for general spectral rectangle 458. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0458
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5494469886, 5303035727, 5120270295, 4945677510, 4778796313, 4619197619, 4466481587, 4320275181, 4180229985, 4046020227, 3917341003, 3793906673, 3675449396, 3561717811, 3452475826, 3347501520, 3246586139, 3149533171, 3056157504, 2966284652, 2879750036, 2796398334, 2716082869, 2638665052, 2564013864, 2492005375, 2422522303, 2355453599, 2290694066, 2228144001, 2167708867, 2109298984, 2052829241, 1998218826, 1945390982, 1894272766, 1844794837, 1796891246, 1750499251, 1705559132, 1662014027, 1619809775, 1578894763, 1539219795, 1500737957, 1463404494, 1427176700, 1392013805, 1357876874, 1324728715, 1292533783, 1261258101, 1230869175, 1201335920, 1172628591, 1144718714, 1117579020, 1091183391, 1065506797, 1040525247, 1016215739, 992556206, 969525478, 947103237, 925269974, 904006952, 883296173, 863120339, 843462822, 824307631, 805639387, 787443290, 769705097, 752411095, 735548077, 719103320, 703064564, 687419993, 672158211, 657268229, 642739446, 628561630, 614724907, 601219741, 588036922, 575167553, 562603037, 550335065, 538355601, 526656875, 515231371, 504071817, 493171173, 482522626, 472119578, 461955638, 452024616, 442320514, 432837517, 423569989, 414512466, 405659645, 397006387, 388547701, 380278747, 372194824, 364291369, 356563952, 349008269, 341620139, 334395501, 327330406, 320421017, 313663604, 307054541, 300590299, 294267448, 288082649, 282032656, 276114308, 270324528]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 458).prefactor = (5253410152903323/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 458).cutoff/(generalMeanRows 458).c)).2 =
    (74101758748271/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 458).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 458).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 458).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 458

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 458).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 458).criticalRate j.val*(generalMeanRows 458).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 458).c*(generalMeanRows 458).criticalPoint j.val)).2-
      (generalMeanRows 458).J/2-(generalMeanRows 458).error (generalMeanGrid j.val)+
      (generalMeanRows 458).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 458).c)).2-
      (generalMeanRows 458).J/2-(generalMeanRows 458).error 4 := by
  have he : (generalMeanRows 458).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 458) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 458)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0458

/-! Kernel-checked entropy margins for general spectral rectangle 459. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0459
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5638524116, 5458865379, 5287200857, 5123067313, 4966034558, 4815702571, 4671698920, 4533676456, 4401311238, 4274300675, 4152361835, 4035229926, 3922656914, 3814410267, 3710271812, 3610036690, 3513512408, 3420517962, 3330883034, 3244447266, 3161059576, 3080577536, 3002866802, 2927800582, 2855259143, 2785129362, 2717304304, 2651682830, 2588169239, 2526672931, 2467108091, 2409393405, 2353451783, 2299210108, 2246599005, 2195552613, 2146008387, 2097906903, 2051191677, 2005809001, 1961707781, 1918839395, 1877157550, 1836618156, 1797179201, 1758800641, 1721444290, 1685073720, 1649654168, 1615152444, 1581536851, 1548777102, 1516844249, 1485710615, 1455349722, 1425736235, 1396845899, 1368655489, 1341142754, 1314286368, 1288065887, 1262461702, 1237454999, 1213027719, 1189162524, 1165842758, 1143052419, 1120776123, 1098999076, 1077707050, 1056886349, 1036523792, 1016606683, 997122793, 978060335, 959407948, 941154675, 923289944, 905803554, 888685656, 871926740, 855517617, 839449409, 823713532, 808301686, 793205841, 778418229, 763931329, 749737859, 735830766, 722203218, 708848591, 695760466, 682932617, 670359004, 658033769, 645951222, 634105844, 622492272, 611105297, 599939859, 588991038, 578254054, 567724257, 557397125, 547268258, 537333375, 527588310, 518029005, 508651511, 499451979, 490426662, 481571907, 472884155, 464359936, 455995867, 447788648, 439735063, 431831971, 424076310, 416465090]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 459).prefactor = (2475326109888669/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 459).cutoff/(generalMeanRows 459).c)).2 =
    (213446595690371/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 459).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 459).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 459).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 459

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 459).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 459).criticalRate j.val*(generalMeanRows 459).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 459).c*(generalMeanRows 459).criticalPoint j.val)).2-
      (generalMeanRows 459).J/2-(generalMeanRows 459).error (generalMeanGrid j.val)+
      (generalMeanRows 459).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 459).c)).2-
      (generalMeanRows 459).J/2-(generalMeanRows 459).error 4 := by
  have he : (generalMeanRows 459).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 459) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 459)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0459

/-! Kernel-checked entropy margins for general spectral rectangle 460. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0460
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5776976510, 5595813936, 5422689178, 5257135821, 5098720760, 4947041287, 4801722501, 4662414976, 4528792677, 4400551080, 4277405471, 4159089418, 4045353371, 3935963403, 3830700052, 3729357272, 3631741475, 3537670647, 3446973542, 3359488943, 3275064977, 3193558494, 3114834479, 3038765526, 2965231337, 2894118272, 2825318919, 2758731703, 2694260526, 2631814420, 2571307240, 2512657366, 2455787431, 2400624068, 2347097670, 2295142172, 2244694840, 2195696081, 2148089261, 2101820532, 2056838683, 2013094979, 1970543033, 1929138668, 1888839800, 1849606318, 1811399981, 1774184312, 1737924506, 1702587339, 1668141085, 1634555435, 1601801424, 1569851358, 1538678753, 1508258266, 1478565642, 1449577654, 1421272055, 1393627525, 1366623626, 1340240758, 1314460117, 1289263658, 1264634053, 1240554662, 1217009495, 1193983183, 1171460949, 1149428577, 1127872390, 1106779219, 1086136386, 1065931675, 1046153315, 1026789958, 1007830661, 989264865, 971082383, 953273377, 935828348, 918738118, 901993818, 885586874, 869508993, 853752153, 838308593, 823170795, 808331484, 793783611, 779520344, 765535063, 751821350, 738372977, 725183905, 712248273, 699560389, 687114729, 674905926, 662928766, 651178182, 639649247, 628337172, 617237299, 606345095, 595656151, 585166173, 574870983, 564766510, 554848791, 545113964, 535558265, 526178026, 516969670, 507929711, 499054747, 490341461, 481786616, 473387053, 465139687, 457041510]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 460).prefactor = (2492234547573897/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 460).cutoff/(generalMeanRows 460).c)).2 =
    (434893234047819/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 460).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 460).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 460).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 460

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 460).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 460).criticalRate j.val*(generalMeanRows 460).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 460).c*(generalMeanRows 460).criticalPoint j.val)).2-
      (generalMeanRows 460).J/2-(generalMeanRows 460).error (generalMeanGrid j.val)+
      (generalMeanRows 460).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 460).c)).2-
      (generalMeanRows 460).J/2-(generalMeanRows 460).error 4 := by
  have he : (generalMeanRows 460).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 460) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 460)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0460

/-! Kernel-checked entropy margins for general spectral rectangle 461. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0461
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5393170709, 5197729848, 5011210297, 4833104467, 4662940422, 4500278772, 4344709902, 4195851490, 4053346284, 3916860096, 3786079999, 3660712693, 3540483020, 3425132621, 3314418708, 3208112950, 3106000450, 3007878808, 2913557262, 2822855908, 2735604966, 2651644117, 2570821886, 2492995074, 2418028231, 2345793170, 2276168512, 2209039273, 2144296469, 2081836756, 2021562095, 1963379435, 1907200425, 1852941137, 1800521812, 1749866623, 1700903453, 1653563685, 1607782006, 1563496227, 1520647110, 1479178208, 1439035712, 1400168313, 1362527065, 1326065262, 1290738320, 1256503664, 1223320628, 1191150354, 1159955697, 1129701143, 1100352724, 1071877940, 1044245684, 1017426177, 991390901, 966112535, 941564899, 917722899, 894562472, 872060540, 850194962, 828944488, 808288720, 788208070, 768683723, 749697603, 731232337, 713271222, 695798199, 678797819, 662255220, 646156097, 630486680, 615233710, 600384416, 585926494, 571848087, 558137766, 544784512, 531777698, 519107071, 506762741, 494735160, 483015113, 471593701, 460462328, 449612694, 439036773, 428726814, 418675319, 408875041, 399318971, 390000326, 380912548, 372049285, 363404393, 354971921, 346746106, 338721368, 330892301, 323253665, 315800384, 308527538, 301430354, 294504207, 287744610, 281147212, 274707789, 268422244, 262286602, 256297003, 250449698, 244741050, 239167526, 233725693, 228412217, 223223858, 218157470, 213209993]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 461).prefactor = (5380189792068273/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 461).cutoff/(generalMeanRows 461).c)).2 =
    (341442012332633/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 461).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 461).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 461).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 461

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 461).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 461).criticalRate j.val*(generalMeanRows 461).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 461).c*(generalMeanRows 461).criticalPoint j.val)).2-
      (generalMeanRows 461).J/2-(generalMeanRows 461).error (generalMeanGrid j.val)+
      (generalMeanRows 461).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 461).c)).2-
      (generalMeanRows 461).J/2-(generalMeanRows 461).error 4 := by
  have he : (generalMeanRows 461).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 461) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 461)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0461

/-! Kernel-checked entropy margins for general spectral rectangle 462. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0462
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5530632630, 5348927489, 5175328446, 5009369143, 4850616339, 4698667019, 4553145820, 4413702712, 4280010932, 4151765112, 4028679600, 3910486930, 3796936444, 3687793037, 3582836008, 3481858024, 3384664163, 3291071039, 3200906007, 3114006424, 3030218973, 2949399042, 2871410150, 2796123413, 2723417060, 2653175972, 2585291266, 2519659905, 2456184335, 2394772147, 2335335767, 2277792163, 2222062574, 2168072255, 2115750247, 2065029148, 2015844913, 1968136661, 1921846491, 1876919317, 1833302711, 1790946749, 1749803879, 1709828787, 1670978274, 1633211145, 1596488097, 1560771620, 1526025902, 1492216738, 1459311445, 1427278784, 1396088884, 1365713175, 1336124314, 1307296131, 1279203564, 1251822605, 1225130247, 1199104436, 1173724022, 1148968713, 1124819040, 1101256309, 1078262568, 1055820572, 1033913747, 1012526159, 991642487, 971247988, 951328478, 931870300, 912860303, 894285817, 876134635, 858394988, 841055527, 824105307, 807533764, 791330702, 775486279, 759990987, 744835639, 730011359, 715509563, 701321954, 687440502, 673857439, 660565248, 647556648, 634824589, 622362243, 610162992, 598220421, 586528313, 575080635, 563871538, 552895345, 542146548, 531619797, 521309900, 511211812, 501320633, 491631601, 482140089, 472841595, 463731746, 454806285, 446061073, 437492082, 429095392, 420867186, 412803750, 404901464, 397156806, 389566343, 382126729, 374834704, 367687093, 360680797, 353812796]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 462).prefactor = (4993113878191157/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 462).cutoff/(generalMeanRows 462).c)).2 =
    (405217465901701/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 462).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 462).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 462).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 462

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 462).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 462).criticalRate j.val*(generalMeanRows 462).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 462).c*(generalMeanRows 462).criticalPoint j.val)).2-
      (generalMeanRows 462).J/2-(generalMeanRows 462).error (generalMeanGrid j.val)+
      (generalMeanRows 462).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 462).c)).2-
      (generalMeanRows 462).J/2-(generalMeanRows 462).error 4 := by
  have he : (generalMeanRows 462).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 462) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 462)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0462

/-! Kernel-checked entropy margins for general spectral rectangle 463. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0463
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5665552784, 5482215202, 5307029740, 5139526870, 4979270433, 4825854735, 4678901938, 4538059740, 4402999277, 4273413249, 4149014217, 4029533069, 3914717626, 3804331377, 3698152327, 3595971944, 3497594199, 3402834688, 3311519820, 3223486082, 3138579353, 3056654280, 2977573695, 2901208086, 2827435095, 2756139069, 2687210630, 2620546284, 2556048059, 2493623159, 2433183656, 2374646191, 2317931704, 2262965177, 2209675396, 2157994730, 2107858923, 2059206900, 2011980585, 1966124730, 1921586759, 1878316616, 1836266628, 1795391368, 1755647539, 1716993854, 1679390929, 1642801179, 1607188725, 1572519301, 1538760170, 1505880044, 1473849009, 1442638454, 1412221003, 1382570452, 1353661712, 1325470750, 1297974536, 1271150996, 1244978960, 1219438123, 1194508999, 1170172881, 1146411805, 1123208515, 1100546426, 1078409596, 1056782693, 1035650966, 1015000222, 994816797, 975087530, 955799744, 936941222, 918500188, 900465284, 882825554, 865570426, 848689695, 832173507, 816012342, 800197003, 784718602, 769568542, 754738512, 740220469, 726006631, 712089464, 698461671, 685116188, 672046166, 659244972, 646706171, 634423526, 622390986, 610602680, 599052910, 587736144, 576647013, 565780299, 555130935, 544693994, 534464691, 524438372, 514610509, 504976702, 495532667, 486274237, 477197355, 468298072, 459572542, 451017021, 442627859, 434401502, 426334486, 418423435, 410665056, 403056140, 395593557, 388274254]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 463).prefactor = (5027778678769581/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 463).cutoff/(generalMeanRows 463).c)).2 =
    (6454555036447/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 463).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 463).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 463).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 463

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 463).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 463).criticalRate j.val*(generalMeanRows 463).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 463).c*(generalMeanRows 463).criticalPoint j.val)).2-
      (generalMeanRows 463).J/2-(generalMeanRows 463).error (generalMeanGrid j.val)+
      (generalMeanRows 463).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 463).c)).2-
      (generalMeanRows 463).J/2-(generalMeanRows 463).error 4 := by
  have he : (generalMeanRows 463).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 463) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 463)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0463

/-! Kernel-checked entropy margins for general spectral rectangle 464. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0464
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5339493294, 5156358130, 4981449918, 4814298764, 4654467960, 4501551091, 4355169450, 4214969726, 4080621931, 3951817528, 3828267753, 3709702082, 3595866854, 3486524015, 3381449973, 3280434555, 3183280055, 3089800362, 2999820155, 2913174176, 2829706546, 2749270146, 2671726044, 2596942963, 2524796787, 2455170115, 2387951833, 2323036726, 2260325118, 2199722532, 2141139378, 2084490659, 2029695703, 1976677907, 1925364500, 1875686322, 1827577617, 1780975843, 1735821486, 1692057893, 1649631114, 1608489752, 1568584824, 1529869628, 1492299623, 1455832311, 1420427128, 1386045346, 1352649970, 1320205653, 1288678608, 1258036527, 1228248509, 1199284986, 1171117654, 1143719412, 1117064303, 1091127454, 1065885025, 1041314159, 1017392930, 994100304, 971416091, 949320909, 927796141, 906823904, 886387010, 866468937, 847053795, 828126303, 809671752, 791675987, 774125379, 757006801, 740307606, 724015606, 708119053, 692606616, 677467368, 662690765, 648266631, 634185142, 620436810, 607012473, 593903275, 581100660, 568596355, 556382360, 544450937, 532794600, 521406104, 510278436, 499404806, 488778637, 478393558, 468243397, 458322171, 448624079, 439143498, 429874975, 420813217, 411953092, 403289617, 394817955, 386533411, 378431425, 370507567, 362757535, 355177147, 347762340, 340509164, 333413778, 326472447, 319681540, 313037523, 306536959, 300176503, 293952899, 287862978, 281903655, 276071926]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 464).prefactor = (157410540540467/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 464).cutoff/(generalMeanRows 464).c)).2 =
    (188064841713321/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 464).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 464).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 464).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 464

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 464).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 464).criticalRate j.val*(generalMeanRows 464).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 464).c*(generalMeanRows 464).criticalPoint j.val)).2-
      (generalMeanRows 464).J/2-(generalMeanRows 464).error (generalMeanGrid j.val)+
      (generalMeanRows 464).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 464).c)).2-
      (generalMeanRows 464).J/2-(generalMeanRows 464).error 4 := by
  have he : (generalMeanRows 464).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 464) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 464)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0464

/-! Kernel-checked entropy margins for general spectral rectangle 465. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0465
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5468393705, 5283470548, 5106823582, 4937979763, 4776499487, 4621973671, 4474021152, 4332286351, 4196437191, 4066163204, 3941173842, 3821196931, 3705977287, 3595275446, 3488866509, 3386539096, 3288094382, 3193345219, 3102115329, 3014238561, 2929558213, 2847926403, 2769203489, 2693257538, 2619963826, 2549204387, 2480867582, 2414847712, 2351044650, 2289363500, 2229714285, 2172011650, 2116174587, 2062126183, 2009793379, 1959106749, 1910000290, 1862411225, 1816279829, 1771549249, 1728165348, 1686076559, 1645233735, 1605590026, 1567100751, 1529723281, 1493416930, 1458142856, 1423863955, 1390544782, 1358151454, 1326651575, 1296014160, 1266209561, 1237209400, 1208986505, 1181514850, 1154769498, 1128726549, 1103363084, 1078657123, 1054587576, 1031134201, 1008277564, 985998999, 964280573, 943105053, 922455870, 902317089, 882673383, 863510000, 844812743, 826567938, 808762415, 791383486, 774418921, 757856928, 741686136, 725895575, 710474660, 695413172, 680701244, 666329349, 652288279, 638569138, 625163325, 612062526, 599258697, 586744058, 574511077, 562552467, 550861169, 539430350, 528253388, 517323867, 506635569, 496182467, 485958714, 475958641, 466176748, 456607697, 447246308, 438087552, 429126545, 420358545, 411778944, 403383266, 395167159, 387126395, 379256862, 371554563, 364015607, 356636214, 349412702, 342341490, 335419092, 328642114, 322007252, 315511289, 309151091, 302923605]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 465).prefactor = (1014537250192863/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 465).cutoff/(generalMeanRows 465).c)).2 =
    (191911014524899/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 465).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 465).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 465).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 465

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 465).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 465).criticalRate j.val*(generalMeanRows 465).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 465).c*(generalMeanRows 465).criticalPoint j.val)).2-
      (generalMeanRows 465).J/2-(generalMeanRows 465).error (generalMeanGrid j.val)+
      (generalMeanRows 465).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 465).c)).2-
      (generalMeanRows 465).J/2-(generalMeanRows 465).error 4 := by
  have he : (generalMeanRows 465).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 465) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 465)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0465

/-! Kernel-checked entropy margins for general spectral rectangle 466. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0466
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5905967260, 5720740455, 5543700472, 5374374551, 5212323596, 5057139237, 4908441204, 4765874981, 4629109692, 4497836209, 4371765435, 4250626752, 4134166622, 4022147300, 3914345681, 3810552232, 3710570025, 3614213847, 3521309389, 3431692495, 3345208477, 3261711478, 3181063891, 3103135818, 3027804571, 2954954210, 2884475118, 2816263600, 2750221519, 2686255950, 2624278865, 2564206832, 2505960747, 2449465568, 2394650079, 2341446667, 2289791112, 2239622387, 2190882482, 2143516226, 2097471131, 2052697240, 2009146984, 1966775053, 1925538271, 1885395477, 1846307420, 1808236651, 1771147429, 1735005631, 1699778664, 1665435386, 1631946030, 1599282131, 1567416461, 1536322963, 1505976693, 1476353763, 1447431288, 1419187335, 1391600876, 1364651741, 1338320580, 1312588821, 1287438629, 1262852876, 1238815101, 1215309483, 1192320808, 1169834441, 1147836300, 1126312829, 1105250971, 1084638151, 1064462250, 1044711583, 1025374886, 1006441288, 987900300, 969741796, 951955999, 934533462, 917465056, 900741958, 884355634, 868297830, 852560559, 837136091, 822016938, 807195852, 792665807, 778419996, 764451819, 750754875, 737322955, 724150035, 711230269, 698557978, 686127649, 673933927, 661971608, 650235633, 638721085, 627423181, 616337271, 605458829, 594783450, 584306846, 574024844, 563933378, 554028489, 544306317, 534763103, 525395181, 516198979, 507171012, 498307881, 489606270, 481062946, 472674751, 464438602]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 466).prefactor = (1265671035118051/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 466).cutoff/(generalMeanRows 466).c)).2 =
    (21451405729771/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 466).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 466).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 466).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 466

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 466).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 466).criticalRate j.val*(generalMeanRows 466).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 466).c*(generalMeanRows 466).criticalPoint j.val)).2-
      (generalMeanRows 466).J/2-(generalMeanRows 466).error (generalMeanGrid j.val)+
      (generalMeanRows 466).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 466).c)).2-
      (generalMeanRows 466).J/2-(generalMeanRows 466).error 4 := by
  have he : (generalMeanRows 466).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 466) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 466)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0466

/-! Kernel-checked entropy margins for general spectral rectangle 467. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0467
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5151804435, 4981868068, 4819572481, 4664472833, 4516156149, 4374238535, 4238362694, 4108195698, 3983426985, 3863766560, 3748943370, 3638703826, 3532810473, 3431040777, 3333186017, 3239050277, 3148449529, 3061210783, 2977171321, 2896177980, 2818086504, 2742760941, 2670073088, 2599901981, 2532133420, 2466659533, 2403378373, 2342193537, 2283013822, 2225752902, 2170329024, 2116664730, 2064686595, 2014324989, 1965513845, 1918190449, 1872295249, 1827771662, 1784565909, 1742626848, 1701905831, 1662356556, 1623934939, 1586598987, 1550308685, 1515025886, 1480714210, 1447338943, 1414866955, 1383266606, 1352507676, 1322561282, 1293399811, 1264996854, 1237327144, 1210366493, 1184091743, 1158480708, 1133512128, 1109165620, 1085421638, 1062261429, 1039666991, 1017621044, 996106986, 975108868, 954611358, 934599712, 915059748, 895977819, 877340787, 859136000, 841351272, 823974855, 806995430, 790402075, 774184258, 758331814, 742834931, 727684132, 712870265, 698384483, 684218238, 670363262, 656811560, 643555395, 630587280, 617899965, 605486432, 593339880, 581453720, 569821566, 558437227, 547294697, 536388153, 525711942, 515260579, 505028739, 495011251, 485203092, 475599382, 466195381, 456986478, 447968193, 439136168, 430486166, 422014064, 413715848, 405587615, 397625564, 389825993, 382185299, 374699972, 367366591, 360181824, 353142425, 346245228, 339487147, 332865174, 326376375, 320017888]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 467).prefactor = (1198649269830967/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 467).cutoff/(generalMeanRows 467).c)).2 =
    (418778741453197/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 467).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 467).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 467).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 467

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 467).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 467).criticalRate j.val*(generalMeanRows 467).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 467).c*(generalMeanRows 467).criticalPoint j.val)).2-
      (generalMeanRows 467).J/2-(generalMeanRows 467).error (generalMeanGrid j.val)+
      (generalMeanRows 467).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 467).c)).2-
      (generalMeanRows 467).J/2-(generalMeanRows 467).error 4 := by
  have he : (generalMeanRows 467).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 467) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 467)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0467

/-! Kernel-checked entropy margins for general spectral rectangle 468. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0468
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5696986856, 5509874095, 5331076599, 5160118232, 4996556580, 4839980002, 4690005008, 4546273908, 4408452698, 4276229165, 4149311173, 4027425111, 3910314488, 3797738659, 3689471657, 3585301136, 3485027403, 3388462527, 3295429527, 3205761625, 3119301557, 3035900943, 2955419698, 2877725498, 2802693278, 2730204771, 2660148082, 2592417288, 2526912073, 2463537384, 2402203111, 2342823793, 2285318342, 2229609782, 2175625010, 2123294574, 2072552459, 2023335893, 1975585163, 1929243443, 1884256632, 1840573205, 1798144067, 1756922425, 1716863661, 1677925214, 1640066470, 1603248660, 1567434761, 1532589404, 1498678788, 1465670599, 1433533933, 1402239226, 1371758181, 1342063707, 1313129859, 1284931779, 1257445644, 1230648611, 1204518774, 1179035114, 1154177458, 1129926440, 1106263458, 1083170640, 1060630813, 1038627462, 1017144706, 996167268, 975680444, 955670079, 936122540, 917024696, 898363893, 880127931, 862305048, 844883897, 827853531, 811203383, 794923250, 779003280, 763433953, 748206070, 733310739, 718739361, 704483619, 690535466, 676887113, 663531021, 650459890, 637666647, 625144440, 612886630, 600886778, 589138642, 577636168, 566373481, 555344883, 544544838, 533967977, 523609081, 513463083, 503525060, 493790227, 484253933, 474911655, 465758997, 456791681, 448005546, 439396543, 430960730, 422694272, 414593432, 406654573, 398874152, 391248717, 383774904, 376449436, 369269118, 362230834]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 468).prefactor = (2554243043418843/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 468).cutoff/(generalMeanRows 468).c)).2 =
    (39938654559091/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 468).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 468).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 468).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 468

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 468).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 468).criticalRate j.val*(generalMeanRows 468).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 468).c*(generalMeanRows 468).criticalPoint j.val)).2-
      (generalMeanRows 468).J/2-(generalMeanRows 468).error (generalMeanGrid j.val)+
      (generalMeanRows 468).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 468).c)).2-
      (generalMeanRows 468).J/2-(generalMeanRows 468).error 4 := by
  have he : (generalMeanRows 468).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 468) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 468)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0468

/-! Kernel-checked entropy margins for general spectral rectangle 469. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0469
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5937316618, 5748158287, 5567352549, 5394420029, 5228915361, 5070424220, 4918560674, 4772964805, 4633300590, 4499253977, 4370531160, 4246857011, 4127973667, 4013639238, 3903626634, 3797722495, 3695726213, 3597449037, 3502713250, 3411351418, 3323205692, 3238127171, 3155975316, 3076617400, 2999928006, 2925788566, 2854086924, 2784716938, 2717578107, 2652575227, 2589618069, 2528621079, 2469503101, 2412187115, 2356599996, 2302672284, 2250337979, 2199534335, 2150201683, 2102283248, 2055724995, 2010475473, 1966485671, 1923708887, 1882100600, 1841618352, 1802221637, 1763871797, 1726531924, 1690166767, 1654742646, 1620227367, 1586590149, 1553801550, 1521833396, 1490658719, 1460251696, 1430587588, 1401642693, 1373394286, 1345820575, 1318900656, 1292614469, 1266942755, 1241867020, 1217369496, 1193433108, 1170041442, 1147178712, 1124829731, 1102979885, 1081615101, 1060721832, 1040287024, 1020298097, 1000742923, 981609809, 962887474, 944565030, 926631969, 909078143, 891893751, 875069321, 858595698, 842464033, 826665763, 811192606, 796036548, 781189828, 766644933, 752394584, 738431730, 724749534, 711341369, 698200810, 685321623, 672697757, 660323343, 648192680, 636300233, 624640626, 613208634, 601999181, 591007331, 580228287, 569657380, 559290071, 549121943, 539148695, 529366143, 519770212, 510356933, 501122440, 492062966, 483174842, 474454489, 465898421, 457503236, 449265617, 441182331, 433250220]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 469).prefactor = (5144538575484189/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 469).cutoff/(generalMeanRows 469).c)).2 =
    (415197151617551/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 469).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 469).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 469).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 469

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 469).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 469).criticalRate j.val*(generalMeanRows 469).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 469).c*(generalMeanRows 469).criticalPoint j.val)).2-
      (generalMeanRows 469).J/2-(generalMeanRows 469).error (generalMeanGrid j.val)+
      (generalMeanRows 469).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 469).c)).2-
      (generalMeanRows 469).J/2-(generalMeanRows 469).error 4 := by
  have he : (generalMeanRows 469).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 469) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 469)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0469

/-! Kernel-checked entropy margins for general spectral rectangle 470. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0470
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6223419453, 6025099034, 5835578115, 5654350260, 5480944973, 5314924568, 5155881361, 5003435167, 4857231055, 4716937315, 4582243641, 4452859472, 4328512493, 4208947281, 4093924055, 3983217552, 3876615992, 3773920130, 3674942389, 3579506064, 3487444585, 3398600846, 3312826580, 3229981782, 3149934179, 3072558737, 2997737205, 2925357690, 2855314265, 2787506605, 2721839642, 2658223256, 2596571974, 2536804695, 2478844439, 2422618102, 2368056231, 2315092819, 2263665109, 2213713403, 2165180899, 2118013526, 2072159790, 2027570638, 1984199320, 1942001265, 1900933966, 1860956866, 1822031255, 1784120173, 1747188319, 1711201961, 1676128857, 1641938177, 1608600431, 1576087398, 1544372067, 1513428570, 1483232129, 1453758998, 1424986415, 1396892551, 1369456467, 1342658067, 1316478060, 1290897921, 1265899851, 1241466749, 1217582171, 1194230306, 1171395942, 1149064441, 1127221709, 1105854175, 1084948765, 1064492880, 1044474373, 1024881532, 1005703059, 986928049, 968545979, 950546685, 932920349, 915657487, 898748930, 882185812, 865959561, 850061879, 834484740, 819220372, 804261247, 789600077, 775229795, 761143555, 747334719, 733796849, 720523698, 707509205, 694747489, 682232838, 669959704, 657922700, 646116589, 634536283, 623176835, 612033433, 601101399, 590376180, 579853346, 569528586, 559397700, 549456601, 539701307, 530127939, 520732717, 511511957, 502462067, 493579546, 484860979, 476303035, 467902465]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 470).prefactor = (2683704038315881/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 470).cutoff/(generalMeanRows 470).c)).2 =
    (418518012927717/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 470).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 470).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 470).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 470

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 470).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 470).criticalRate j.val*(generalMeanRows 470).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 470).c*(generalMeanRows 470).criticalPoint j.val)).2-
      (generalMeanRows 470).J/2-(generalMeanRows 470).error (generalMeanGrid j.val)+
      (generalMeanRows 470).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 470).c)).2-
      (generalMeanRows 470).J/2-(generalMeanRows 470).error 4 := by
  have he : (generalMeanRows 470).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 470) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 470)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0470

/-! Kernel-checked entropy margins for general spectral rectangle 471. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0471
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5033286464, 4860052575, 4694721516, 4536832824, 4385958980, 4241702528, 4103693509, 3971587159, 3845061842, 3723817192, 3607572427, 3496064832, 3389048378, 3286292470, 3187580801, 3092710315, 3001490252, 2913741277, 2829294683, 2747991653, 2669682586, 2594226481, 2521490355, 2451348723, 2383683102, 2318381564, 2255338315, 2194453306, 2135631874, 2078784408, 2023826038, 1970676343, 1919259085, 1869501957, 1821336348, 1774697126, 1729522434, 1685753500, 1643334456, 1602212176, 1562336117, 1523658176, 1486132549, 1449715608, 1414365776, 1380043417, 1346710731, 1314331653, 1282871759, 1252298180, 1222579518, 1193685770, 1165588254, 1138259540, 1111673385, 1085804674, 1060629360, 1036124410, 1012267758, 989038250, 966415603, 944380362, 922913859, 901998172, 881616092, 861751089, 842387278, 823509386, 805102730, 787153184, 769647152, 752571550, 735913777, 719661693, 703803603, 688328232, 673224708, 658482547, 644091630, 630042193, 616324808, 602930371, 589850087, 577075455, 564598260, 552410559, 540504668, 528873153, 517508822, 506404712, 495554079, 484950395, 474587333, 464458763, 454558743, 444881513, 435421486, 426173244, 417131529, 408291240, 399647424, 391195273, 382930118, 374847425, 366942786, 359211922, 351650670, 344254987, 337020940, 329944703, 323022558, 316250886, 309626165, 303144968, 296803962, 290599899, 284529617, 278590038, 272778165, 267091075, 261525925]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 471).prefactor = (615524730501991/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 471).cutoff/(generalMeanRows 471).c)).2 =
    (200247466686133/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 471).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 471).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 471).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 471

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 471).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 471).criticalRate j.val*(generalMeanRows 471).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 471).c*(generalMeanRows 471).criticalPoint j.val)).2-
      (generalMeanRows 471).J/2-(generalMeanRows 471).error (generalMeanGrid j.val)+
      (generalMeanRows 471).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 471).c)).2-
      (generalMeanRows 471).J/2-(generalMeanRows 471).error 4 := by
  have he : (generalMeanRows 471).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 471) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 471)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0471

/-! Kernel-checked entropy margins for general spectral rectangle 472. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0472
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6008606893, 5808220842, 5616773662, 5433755106, 5258690949, 5091139841, 4930690509, 4776959241, 4629587639, 4488240589, 4352604437, 4222385329, 4097307719, 3977113001, 3861558273, 3750415205, 3643469003, 3540517464, 3441370112, 3345847393, 3253779948, 3165007935, 3079380408, 2996754738, 2916996083, 2839976897, 2765576470, 2693680506, 2624180731, 2556974523, 2491964576, 2429058583, 2368168936, 2309212455, 2252110129, 2196786876, 2143171318, 2091195570, 2040795046, 1991908272, 1944476714, 1898444616, 1853758850, 1810368769, 1768226078, 1727284703, 1687500679, 1648832032, 1611238677, 1574682321, 1539126368, 1504535831, 1470877251, 1438118621, 1406229306, 1375179981, 1344942563, 1315490145, 1286796947, 1258838252, 1231590357, 1205030527, 1179136943, 1153888662, 1129265573, 1105248359, 1081818458, 1058958031, 1036649923, 1014877637, 993625298, 972877631, 952619928, 932838026, 913518281, 894647546, 876213147, 858202865, 840604912, 823407918, 806600907, 790173284, 774114819, 758415628, 743066161, 728057189, 713379789, 699025331, 684985467, 671252119, 657817471, 644673952, 631814233, 619231214, 606918016, 594867972, 583074617, 571531685, 560233098, 549172957, 538345542, 527745297, 517366830, 507204905, 497254437, 487510485, 477968246, 468623056, 459470378, 450505801, 441725035, 433123908, 424698360, 416444440, 408358303, 400436205, 392674503, 385069646, 377618177, 370316728, 363162017]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 472).prefactor = (5419474409823687/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 472).cutoff/(generalMeanRows 472).c)).2 =
    (388325598231483/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 472).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 472).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 472).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 472

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 472).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 472).criticalRate j.val*(generalMeanRows 472).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 472).c*(generalMeanRows 472).criticalPoint j.val)).2-
      (generalMeanRows 472).J/2-(generalMeanRows 472).error (generalMeanGrid j.val)+
      (generalMeanRows 472).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 472).c)).2-
      (generalMeanRows 472).J/2-(generalMeanRows 472).error 4 := by
  have he : (generalMeanRows 472).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 472) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 472)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0472

/-! Kernel-checked entropy margins for general spectral rectangle 473. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0473
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5232652576, 5062675576, 4900340928, 4745201083, 4596840683, 4454873745, 4318941155, 4188708408, 4063863585, 3944115537, 3829192233, 3718839274, 3612818541, 3510906966, 3412895417, 3318587676, 3227799507, 3140357802, 3056099799, 2974872365, 2896531331, 2820940891, 2747973034, 2677507029, 2609428951, 2543631232, 2480012256, 2418475979, 2358931575, 2301293112, 2245479243, 2191412933, 2139021184, 2088234802, 2038988158, 1991218984, 1944868170, 1899879577, 1856199868, 1813778343, 1772566787, 1732519330, 1693592314, 1655744165, 1618935283, 1583127925, 1548286107, 1514375508, 1481363376, 1449218447, 1417910860, 1387412089, 1357694865, 1328733115, 1300501897, 1272977340, 1246136594, 1219957769, 1194419894, 1169502866, 1145187406, 1121455023, 1098287968, 1075669200, 1053582354, 1032011704, 1010942135, 990359112, 970248653, 950597303, 931392108, 912620595, 894270744, 876330972, 858790113, 841637395, 824862426, 808455178, 792405964, 776705433, 761344547, 746314571, 731607062, 717213852, 703127038, 689338974, 675842256, 662629715, 649694406, 637029600, 624628772, 612485598, 600593945, 588947861, 577541572, 566369471, 555426117, 544706224, 534204656, 523916424, 513836677, 503960702, 494283913, 484801851, 475510177, 466404669, 457481218, 448735825, 440164593, 431763729, 423529537, 415458416, 407546858, 399791443, 392188836, 384735786, 377429124, 370265755, 363242665, 356356908, 349605613]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 473).prefactor = (4817202937555087/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 473).cutoff/(generalMeanRows 473).c)).2 =
    (432277485760663/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 473).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 473).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 473).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 473

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 473).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 473).criticalRate j.val*(generalMeanRows 473).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 473).c*(generalMeanRows 473).criticalPoint j.val)).2-
      (generalMeanRows 473).J/2-(generalMeanRows 473).error (generalMeanGrid j.val)+
      (generalMeanRows 473).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 473).c)).2-
      (generalMeanRows 473).J/2-(generalMeanRows 473).error 4 := by
  have he : (generalMeanRows 473).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 473) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 473)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0473

/-! Kernel-checked entropy margins for general spectral rectangle 474. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0474
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5120258004, 4948865544, 4785233867, 4628909460, 4479471368, 4336528347, 4199716322, 4068696115, 3943151392, 3822786829, 3707326443, 3596512090, 3490102096, 3387870022, 3289603526, 3195103339, 3104182319, 3016664589, 2932384749, 2851187143, 2772925198, 2697460808, 2624663764, 2554411232, 2486587275, 2421082398, 2357793138, 2296621683, 2237475509, 2180267058, 2124913422, 2071336067, 2019460557, 1969216316, 1920536389, 1873357232, 1827618510, 1783262906, 1740235951, 1698485857, 1657963360, 1618621586, 1580415905, 1543303814, 1507244815, 1472200303, 1438133464, 1405009178, 1372793925, 1341455700, 1310963934, 1281289413, 1252404212, 1224281622, 1196896092, 1170223165, 1144239426, 1118922442, 1094250721, 1070203656, 1046761489, 1023905262, 1001616780, 979878576, 958673871, 937986544, 917801101, 898102641, 878876833, 860109886, 841788524, 823899964, 806431890, 789372436, 772710162, 756434038, 740533422, 724998045, 709817995, 694983702, 680485919, 666315713, 652464451, 638923783, 625685635, 612742196, 600085907, 587709449, 575605736, 563767905, 552189305, 540863492, 529784218, 518945424, 508341235, 497965949, 487814034, 477880119, 468158991, 458645585, 449334984, 440222407, 431303211, 422572880, 414027025, 405661378, 397471787, 389454211, 381604722, 373919493, 366394800, 359027019, 351812618, 344748158, 337830291, 331055752, 324421362, 317924019, 311560703, 305328468, 299224442]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 474).prefactor = (609866945105453/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 474).cutoff/(generalMeanRows 474).c)).2 =
    (26066754193571/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 474).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 474).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 474).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 474

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 474).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 474).criticalRate j.val*(generalMeanRows 474).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 474).c*(generalMeanRows 474).criticalPoint j.val)).2-
      (generalMeanRows 474).J/2-(generalMeanRows 474).error (generalMeanGrid j.val)+
      (generalMeanRows 474).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 474).c)).2-
      (generalMeanRows 474).J/2-(generalMeanRows 474).error 4 := by
  have he : (generalMeanRows 474).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 474) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 474)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0474

/-! Kernel-checked entropy margins for general spectral rectangle 475. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0475
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5811240402, 5609149911, 5416136003, 5231684120, 5055315841, 4886585730, 4725078529, 4570406636, 4422207853, 4280143353, 4143895851, 4013167944, 3887680613, 3767171857, 3651395454, 3540119825, 3433127002, 3330211680, 3231180347, 3135850488, 3044049848, 2955615760, 2870394515, 2788240795, 2709017130, 2632593412, 2558846433, 2487659465, 2418921862, 2352528694, 2288380408, 2226382508, 2166445260, 2108483415, 2052415950, 1998165828, 1945659773, 1894828056, 1845604302, 1797925298, 1751730826, 1706963496, 1663568596, 1621493943, 1580689755, 1541108518, 1502704872, 1465435492, 1429258990, 1394135809, 1360028131, 1326899791, 1294716189, 1263444217, 1233052177, 1203509719, 1174787769, 1146858467, 1119695111, 1093272098, 1067564872, 1042549875, 1018204495, 994507029, 971436633, 948973286, 927097749, 905791533, 885036859, 864816632, 845114403, 825914346, 807201227, 788960378, 771177671, 753839498, 736932744, 720444766, 704363377, 688676820, 673373756, 658443240, 643874711, 629657969, 615783168, 602240791, 589021649, 576116855, 563517822, 551216245, 539204091, 527473589, 516017221, 504827707, 493898001, 483221281, 472790938, 462600568, 452643968, 442915126, 433408210, 424117570, 415037723, 406163352, 397489297, 389010550, 380722254, 372619688, 364698272, 356953556, 349381218, 341977059, 334736999, 327657072, 320733423, 313962303, 307340069, 300863175, 294528174, 288331711, 282270523]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 475).prefactor = (5473565403297109/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 475).cutoff/(generalMeanRows 475).c)).2 =
    (44842994020221/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 475).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 475).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 475).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 475

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 475).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 475).criticalRate j.val*(generalMeanRows 475).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 475).c*(generalMeanRows 475).criticalPoint j.val)).2-
      (generalMeanRows 475).J/2-(generalMeanRows 475).error (generalMeanGrid j.val)+
      (generalMeanRows 475).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 475).c)).2-
      (generalMeanRows 475).J/2-(generalMeanRows 475).error 4 := by
  have he : (generalMeanRows 475).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 475) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 475)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0475

/-! Kernel-checked entropy margins for general spectral rectangle 476. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0476
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5043838654, 4872529556, 4708980041, 4552739181, 4403388288, 4260538098, 4123826255, 3992915062, 3867489457, 3747255189, 3631937175, 3521278014, 3415036633, 3312987062, 3214917318, 3120628384, 3029933276, 2942656194, 2858631740, 2777704194, 2699726863, 2624561463, 2552077568, 2482152085, 2414668780, 2349517837, 2286595443, 2225803412, 2167048832, 2110243738, 2055304808, 2002153077, 1950713678, 1900915594, 1852691428, 1805977192, 1760712106, 1716838412, 1674301201, 1633048248, 1593029859, 1554198733, 1516509822, 1479920210, 1444388994, 1409877173, 1376347545, 1343764610, 1312094479, 1281304785, 1251364606, 1222244389, 1193915875, 1166352034, 1139527002, 1113416020, 1087995379, 1063242364, 1039135209, 1015653044, 992775855, 970484440, 948760368, 927585945, 906944174, 886818726, 867193904, 848054617, 829386349, 811175131, 793407522, 776070575, 759151823, 742639253, 726521287, 710786761, 695424908, 680425340, 665778034, 651473309, 637501821, 623854540, 610522743, 597497997, 584772148, 572337311, 560185857, 548310403, 536703802, 525359136, 514269702, 503429009, 492830764, 482468869, 472337411, 462430657, 452743045, 443269178, 434003818, 424941882, 416078433, 407408677, 398927958, 390631752, 382515661, 374575413, 366806852, 359205939, 351768745, 344491447, 337370328, 330401768, 323582246, 316908333, 310376692, 303984072, 297727306, 291603312, 285609085, 279741698, 273998298]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 476).prefactor = (4857015098832597/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 476).cutoff/(generalMeanRows 476).c)).2 =
    (201842057615357/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 476).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 476).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 476).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 476

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 476).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 476).criticalRate j.val*(generalMeanRows 476).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 476).c*(generalMeanRows 476).criticalPoint j.val)).2-
      (generalMeanRows 476).J/2-(generalMeanRows 476).error (generalMeanGrid j.val)+
      (generalMeanRows 476).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 476).c)).2-
      (generalMeanRows 476).J/2-(generalMeanRows 476).error 4 := by
  have he : (generalMeanRows 476).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 476) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 476)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0476

/-! Kernel-checked entropy margins for general spectral rectangle 477. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0477
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6083442036, 5892651545, 5710261225, 5535788324, 5368784371, 5208832181, 5055543184, 4908555037, 4767529473, 4632150373, 4502122021, 4377167529, 4257027405, 4141458254, 4030231597, 3923132790, 3819960041, 3720523503, 3624644447, 3532154504, 3442894964, 3356716130, 3273476727, 3193043353, 3115289966, 3040097424, 2967353040, 2896950187, 2828787915, 2762770610, 2698807665, 2636813180, 2576705683, 2518407863, 2461846330, 2406951385, 2353656806, 2301899647, 2251620056, 2202761095, 2155268581, 2109090926, 2064179000, 2020485993, 1977967284, 1936580331, 1896284551, 1857041218, 1818813364, 1781565685, 1745264457, 1709877446, 1675373839, 1641724163, 1608900224, 1576875032, 1545622749, 1515118627, 1485338951, 1456260993, 1427862956, 1400123936, 1373023872, 1346543507, 1320664352, 1295368642, 1270639311, 1246459949, 1222814778, 1199688619, 1177066865, 1154935455, 1133280847, 1112089996, 1091350332, 1071049736, 1051176521, 1031719414, 1012667536, 994010384, 975737819, 957840042, 940307590, 923131310, 906302357, 889812172, 873652475, 857815253, 842292747, 827077443, 812162061, 797539548, 783203065, 769145983, 755361871, 741844489, 728587783, 715585874, 702833056, 690323784, 678052673, 666014489, 654204143, 642616690, 631247317, 620091345, 609144220, 598401508, 587858896, 577512181, 567357273, 557390183, 547607029, 538004025, 528577481, 519323799, 510239470, 501321073, 492565268, 483968800, 475528487]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 477).prefactor = (5180845499968537/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 477).cutoff/(generalMeanRows 477).c)).2 =
    (211598597142313/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 477).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 477).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 477).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 477

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 477).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 477).criticalRate j.val*(generalMeanRows 477).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 477).c*(generalMeanRows 477).criticalPoint j.val)).2-
      (generalMeanRows 477).J/2-(generalMeanRows 477).error (generalMeanGrid j.val)+
      (generalMeanRows 477).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 477).c)).2-
      (generalMeanRows 477).J/2-(generalMeanRows 477).error 4 := by
  have he : (generalMeanRows 477).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 477) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 477)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0477

/-! Kernel-checked entropy margins for general spectral rectangle 478. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0478
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4951036483, 4778141315, 4613112247, 4455494866, 4304867085, 4160836331, 4023037016, 3891128290, 3764792011, 3643730923, 3527667007, 3416339994, 3309506013, 3206936361, 3108416389, 3013744479, 2922731109, 2835198007, 2750977362, 2669911108, 2591850260, 2516654310, 2444190664, 2374334121, 2306966398, 2241975684, 2179256232, 2118707975, 2060236177, 2003751100, 1949167703, 1896405357, 1845387577, 1796041781, 1748299058, 1702093950, 1657364256, 1614050845, 1572097474, 1531450635, 1492059391, 1453875239, 1416851971, 1380945552, 1346113996, 1312317260, 1279517136, 1247677153, 1216762486, 1186739869, 1157577511, 1129245023, 1101713342, 1074954663, 1048942379, 1023651014, 999056171, 975134474, 951863523, 929221838, 907188820, 885744706, 864870528, 844548076, 824759859, 805489074, 786719574, 768435834, 750622923, 733266478, 716352679, 699868219, 683800288, 668136543, 652865095, 637974482, 623453654, 609291955, 595479103, 582005178, 568860604, 556036134, 543522838, 531312087, 519395543, 507765148, 496413108, 485331887, 474514193, 463952971, 453641391, 443572843, 433740924, 424139433, 414762360, 405603883, 396658358, 387920314, 379384444, 371045601, 362898791, 354939169, 347162033, 339562816, 332137087, 324880540, 317788994, 310858386, 304084769, 297464306, 290993269, 284668032, 278485069, 272440952, 266532347, 260756008, 255108779, 249587587, 244189444, 238911438, 233750736]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 478).prefactor = (4898220459239667/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 478).cutoff/(generalMeanRows 478).c)).2 =
    (382983032440467/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 478).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 478).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 478).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 478

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 478).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 478).criticalRate j.val*(generalMeanRows 478).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 478).c*(generalMeanRows 478).criticalPoint j.val)).2-
      (generalMeanRows 478).J/2-(generalMeanRows 478).error (generalMeanGrid j.val)+
      (generalMeanRows 478).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 478).c)).2-
      (generalMeanRows 478).J/2-(generalMeanRows 478).error 4 := by
  have he : (generalMeanRows 478).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 478) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 478)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0478

/-! Kernel-checked entropy margins for general spectral rectangle 479. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0479
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5076563865, 4904143287, 4739532637, 4582278062, 4431958157, 4288181132, 4150582282, 4018821717, 3892582331, 3771567964, 3655501749, 3544124614, 3437193923, 3334482239, 3235776203, 3140875507, 3049591955, 2961748606, 2877178988, 2795726372, 2717243111, 2641590027, 2568635844, 2498256674, 2430335528, 2364761875, 2301431230, 2240244771, 2181108982, 2123935328, 2068639946, 2015143358, 1963370213, 1913249030, 1864711978, 1817694653, 1772135880, 1727977527, 1685164328, 1643643719, 1603365685, 1564282616, 1526349174, 1489522163, 1453760415, 1419024676, 1385277503, 1352483165, 1320607552, 1289618090, 1259483655, 1230174501, 1201662187, 1173919508, 1146920431, 1120640037, 1095054462, 1070140846, 1045877280, 1022242759, 999217139, 976781094, 954916073, 933604267, 912828569, 892572544, 872820393, 853556928, 834767536, 816438162, 798555273, 781105842, 764077318, 747457612, 731235070, 715398456, 699936933, 684840046, 670097705, 655700169, 641638032, 627902206, 614483910, 601374657, 588566241, 576050725, 563820430, 551867926, 540186020, 528767748, 517606364, 506695335, 496028327, 485599202, 475402010, 465430980, 455680513, 446145177, 436819702, 427698971, 418778014, 410052008, 401516265, 393166231, 384997482, 377005716, 369186752, 361536523, 354051075, 346726561, 339559239, 332545466, 325681698, 318964484, 312390464, 305956368, 299659007, 293495280, 287462162, 281556706, 275776042]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 479).prefactor = (488852816934463/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 479).cutoff/(generalMeanRows 479).c)).2 =
    (201842057615357/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 479).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 479).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 479).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 479

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 479).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 479).criticalRate j.val*(generalMeanRows 479).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 479).c*(generalMeanRows 479).criticalPoint j.val)).2-
      (generalMeanRows 479).J/2-(generalMeanRows 479).error (generalMeanGrid j.val)+
      (generalMeanRows 479).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 479).c)).2-
      (generalMeanRows 479).J/2-(generalMeanRows 479).error 4 := by
  have he : (generalMeanRows 479).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 479) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 479)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0479

/-! Kernel-checked entropy margins for general spectral rectangle 480. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0480
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5109501402, 4935962132, 4770283463, 4612008596, 4460713392, 4316003520, 4177511906, 4044896459, 3917838012, 3796038484, 3679219214, 3567119447, 3459494972, 3356116879, 3256770423, 3161253996, 3069378182, 2980964892, 2895846573, 2813865480, 2734873008, 2658729074, 2585301554, 2514465752, 2446103923, 2380104818, 2316363275, 2254779828, 2195260357, 2137715752, 2082061604, 2028217922, 1976108864, 1925662488, 1876810520, 1829488139, 1783633774, 1739188915, 1696097937, 1654307936, 1613768571, 1574431926, 1536252365, 1499186415, 1463192639, 1428231529, 1394265399, 1361258286, 1329175860, 1297985333, 1267655381, 1238156065, 1209458759, 1181536080, 1154361829, 1127910924, 1102159346, 1077084087, 1052663094, 1028875229, 1005700216, 983118602, 961111717, 939661637, 918751143, 898363693, 878483388, 859094938, 840183638, 821735340, 803736424, 786173778, 769034771, 752307234, 735979437, 720040072, 704478233, 689283395, 674445403, 659954454, 645801079, 631976133, 618470777, 605276470, 592384950, 579788232, 567478585, 555448531, 543690831, 532198475, 520964675, 509982853, 499246636, 488749845, 478486492, 468450768, 458637039, 449039837, 439653857, 430473948, 421495111, 412712489, 404121365, 395717155, 387495406, 379451788, 371582093, 363882228, 356348214, 348976177, 341762352, 334703073, 327794772, 321033975, 314417302, 307941460, 301603242, 295399523, 289327261, 283383490, 277565320]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 480).prefactor = (4920245701566761/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 480).cutoff/(generalMeanRows 480).c)).2 =
    (201842057615357/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 480).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 480).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 480).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 480

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 480).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 480).criticalRate j.val*(generalMeanRows 480).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 480).c*(generalMeanRows 480).criticalPoint j.val)).2-
      (generalMeanRows 480).J/2-(generalMeanRows 480).error (generalMeanGrid j.val)+
      (generalMeanRows 480).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 480).c)).2-
      (generalMeanRows 480).J/2-(generalMeanRows 480).error 4 := by
  have he : (generalMeanRows 480).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 480) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 480)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0480

/-! Kernel-checked entropy margins for general spectral rectangle 481. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0481
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4983673066, 4809638196, 4643521278, 4484864903, 4333244205, 4188264018, 4049556348, 3916778097, 3789609027, 3667749919, 3550920925, 3438860059, 3331321842, 3228076065, 3128906663, 3033610687, 2941997369, 2853887261, 2769111444, 2687510811, 2608935397, 2533243765, 2460302448, 2389985420, 2322173618, 2256754494, 2193621603, 2132674220, 2073816983, 2016959564, 1962016361, 1908906212, 1857552130, 1807881053, 1759823616, 1713313930, 1668289384, 1624690456, 1582460535, 1541545757, 1501894851, 1463458994, 1426191674, 1390048564, 1354987403, 1320967883, 1287951545, 1255901677, 1224783225, 1194562702, 1165208110, 1136688858, 1108975692, 1082040624, 1055856870, 1030398787, 1005641818, 981562433, 958138082, 935347146, 913168890, 891583419, 870571641, 850115226, 830196568, 810798753, 791905527, 773501262, 755570931, 738100075, 721074782, 704481659, 688307810, 672540812, 657168696, 642179926, 627563379, 613308327, 599404423, 585841680, 572610459, 559701452, 547105669, 534814426, 522819331, 511112269, 499685398, 488531131, 477642128, 467011288, 456631736, 446496817, 436600088, 426935304, 417496419, 408277571, 399273078, 390477434, 381885297, 373491485, 365290972, 357278882, 349450479, 341801170, 334326491, 327022110, 319883817, 312907523, 306089256, 299425152, 292911459, 286544526, 280320806, 274236847, 268289293, 262474877, 256790422, 251232836, 245799109, 240486311, 235291590]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 481).prefactor = (4930508886108411/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 481).cutoff/(generalMeanRows 481).c)).2 =
    (382983032440467/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 481).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 481).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 481).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 481

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 481).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 481).criticalRate j.val*(generalMeanRows 481).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 481).c*(generalMeanRows 481).criticalPoint j.val)).2-
      (generalMeanRows 481).J/2-(generalMeanRows 481).error (generalMeanGrid j.val)+
      (generalMeanRows 481).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 481).c)).2-
      (generalMeanRows 481).J/2-(generalMeanRows 481).error 4 := by
  have he : (generalMeanRows 481).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 481) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 481)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0481

/-! Kernel-checked entropy margins for general spectral rectangle 482. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0482
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4933562523, 4758928463, 4592272450, 4433133814, 4281084629, 4135726859, 3996689803, 3863627818, 3736218261, 3614159647, 3497169981, 3384985251, 3277358054, 3174056361, 3074862379, 2979571519, 2887991455, 2799941256, 2715250596, 2633759026, 2555315304, 2479776777, 2407008817, 2336884292, 2269283084, 2204091639, 2141202549, 2080514172, 2021930269, 1965359672, 1910715980, 1857917265, 1806885807, 1757547845, 1709833344, 1663675774, 1619011912, 1575781649, 1533927813, 1493396004, 1454134437, 1416093798, 1379227103, 1343489577, 1308838528, 1275233236, 1242634847, 1211006273, 1180312098, 1150518493, 1121593127, 1093505095, 1066224842, 1039724092, 1013975786, 988954018, 964633980, 940991902, 918005006, 895651454, 873910304, 852761462, 832185648, 812164351, 792679793, 773714900, 755253260, 737279099, 719777249, 702733120, 686132673, 669962395, 654209278, 638860793, 623904868, 609329871, 595124591, 581278216, 567780316, 554620831, 541790052, 529278604, 517077436, 505177808, 493571271, 482249664, 471205097, 460429941, 449916817, 439658588, 429648346, 419879407, 410345300, 401039758, 391956710, 383090278, 374434764, 365984645, 357734568, 349679343, 341813934, 334133460, 326633183, 319308504, 312154962, 305168225, 298344085, 291678460, 285167380, 278806991, 272593548, 266523412, 260593044, 254799005, 249137952, 243606633, 238201886, 232920633, 227759883, 222716723, 217788320]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 482).prefactor = (4963010154052473/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 482).cutoff/(generalMeanRows 482).c)).2 =
    (46953757266901/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 482).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 482).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 482).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 482

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 482).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 482).criticalRate j.val*(generalMeanRows 482).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 482).c*(generalMeanRows 482).criticalPoint j.val)).2-
      (generalMeanRows 482).J/2-(generalMeanRows 482).error (generalMeanGrid j.val)+
      (generalMeanRows 482).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 482).c)).2-
      (generalMeanRows 482).J/2-(generalMeanRows 482).error 4 := by
  have he : (generalMeanRows 482).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 482) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 482)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0482

/-! Kernel-checked entropy margins for general spectral rectangle 483. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0483
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5152961705, 4980474541, 4815797729, 4658474859, 4508082288, 4364226272, 4226540413, 4094683364, 3968336772, 3847203426, 3731005581, 3619483443, 3512393797, 3409508753, 3310614617, 3215510846, 3124009103, 3035932387, 2951114241, 2869398017, 2790636204, 2714689813, 2641427805, 2570726563, 2502469406, 2436546141, 2372852646, 2311290481, 2251766533, 2194192685, 2138485499, 2084565938, 2032359094, 1981793936, 1932803085, 1885322589, 1839291728, 1794652820, 1751351047, 1709334289, 1668552971, 1628959916, 1590510211, 1553161081, 1516871768, 1481603422, 1447318994, 1413983139, 1381562124, 1350023738, 1319337218, 1289473162, 1260403467, 1232101255, 1204540810, 1177697521, 1151547820, 1126069134, 1101239831, 1077039175, 1053447280, 1030445067, 1008014226, 986137177, 964797035, 943977576, 923663206, 903838930, 884490325, 865603511, 847165128, 829162311, 811582667, 794414252, 777645555, 761265473, 745263297, 729628694, 714351688, 699422646, 684832264, 670571552, 656631819, 643004665, 629681964, 616655854, 603918727, 591463219, 579282199, 567368758, 555716204, 544318052, 533168013, 522259991, 511588071, 501146517, 490929760, 480932397, 471149178, 461575010, 452204940, 443034160, 434057996, 425271903, 416671465, 408252386, 400010486, 391941702, 384042077, 376307761, 368735008, 361320167, 354059687, 346950106, 339988054, 333170245, 326493480, 319954638, 313550679, 307278638, 301135625]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 483).prefactor = (4910097906528989/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 483).cutoff/(generalMeanRows 483).c)).2 =
    (26066754193571/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 483).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 483).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 483).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 483

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 483).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 483).criticalRate j.val*(generalMeanRows 483).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 483).c*(generalMeanRows 483).criticalPoint j.val)).2-
      (generalMeanRows 483).J/2-(generalMeanRows 483).error (generalMeanGrid j.val)+
      (generalMeanRows 483).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 483).c)).2-
      (generalMeanRows 483).J/2-(generalMeanRows 483).error 4 := by
  have he : (generalMeanRows 483).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 483) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 483)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0483

/-! Kernel-checked entropy margins for general spectral rectangle 484. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0484
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5252239776, 5081452271, 4918316774, 4762386620, 4613247232, 4470513314, 4333826346, 4202852339, 4077279820, 3956818011, 3841195196, 3730157231, 3623466200, 3520899196, 3422247198, 3327314064, 3235915595, 3147878691, 3063040567, 2981248036, 2902356859, 2826231129, 2752742721, 2681770769, 2613201198, 2546926275, 2482844209, 2420858765, 2360878920, 2302818536, 2246596053, 2192134213, 2139359794, 2088203370, 2038599081, 1990484420, 1943800037, 1898489553, 1854499389, 1811778602, 1770278735, 1729953676, 1690759524, 1652654468, 1615598665, 1579554137, 1544484665, 1510355694, 1477134243, 1444788819, 1413289338, 1382607050, 1352714469, 1323585304, 1295194403, 1267517686, 1240532096, 1214215542, 1188546855, 1163505737, 1139072719, 1115229120, 1091957009, 1069239165, 1047059047, 1025400756, 1004249007, 983589101, 963406893, 943688771, 924421625, 905592831, 887190222, 869202071, 851617070, 834424310, 817613266, 801173776, 785096029, 769370546, 753988170, 738940047, 724217617, 709812600, 695716985, 681923019, 668423192, 655210236, 642277106, 629616977, 617223232, 605089455, 593209425, 581577104, 570186634, 559032328, 548108664, 537410280, 526931966, 516668660, 506615441, 496767527, 487120265, 477669131, 468409725, 459337764, 450449079, 441739613, 433205415, 424842637, 416647531, 408616446, 400745824, 393032196, 385472183, 378062488, 370799898, 363681278, 356703571, 349863793, 343159034]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 484).prefactor = (4841604031889871/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 484).cutoff/(generalMeanRows 484).c)).2 =
    (85672309111729/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 484).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 484).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 484).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 484

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 484).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 484).criticalRate j.val*(generalMeanRows 484).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 484).c*(generalMeanRows 484).criticalPoint j.val)).2-
      (generalMeanRows 484).J/2-(generalMeanRows 484).error (generalMeanGrid j.val)+
      (generalMeanRows 484).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 484).c)).2-
      (generalMeanRows 484).J/2-(generalMeanRows 484).error 4 := by
  have he : (generalMeanRows 484).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 484) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 484)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0484

/-! Kernel-checked entropy margins for general spectral rectangle 485. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0485
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5196042646, 5024538831, 4860746412, 4704215747, 4554529464, 4411299635, 4274165266, 4142790029, 4016860245, 3896083049, 3780184748, 3668909324, 3562017086, 3459283436, 3360497750, 3265462356, 3173991604, 3085911004, 3001056449, 2919273493, 2840416689, 2764348980, 2690941137, 2620071242, 2551624210, 2485491344, 2421569924, 2359762831, 2299978190, 2242129045, 2186133055, 2131912209, 2079392565, 2028504002, 1979179992, 1931357391, 1884976233, 1839979547, 1796313186, 1753925658, 1712767983, 1672793541, 1633957944, 1596218913, 1559536156, 1523871259, 1489187588, 1455450185, 1422625682, 1390682214, 1359589340, 1329317965, 1299840271, 1271129650, 1243160641, 1215908869, 1189350993, 1163464649, 1138228404, 1113621707, 1089624847, 1066218909, 1043385737, 1021107894, 999368630, 978151848, 957442071, 937224416, 917484561, 898208725, 879383635, 860996510, 843035035, 825487339, 808341975, 791587905, 775214475, 759211404, 743568765, 728276970, 713326754, 698709165, 684415545, 670437523, 656767000, 643396140, 630317355, 617523299, 605006857, 592761136, 580779453, 569055334, 557582496, 546354849, 535366483, 524611662, 514084818, 503780545, 493693594, 483818865, 474151401, 464686386, 455419139, 446345107, 437459861, 428759097, 420238622, 411894360, 403722340, 395718700, 387879675, 380201602, 372680910, 365314123, 358097850, 351028790, 344103724, 337319511, 330673092, 324161482, 317781771]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 485).prefactor = (2436221492488123/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 485).cutoff/(generalMeanRows 485).c)).2 =
    (210421356572309/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 485).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 485).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 485).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 485

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 485).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 485).criticalRate j.val*(generalMeanRows 485).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 485).c*(generalMeanRows 485).criticalPoint j.val)).2-
      (generalMeanRows 485).J/2-(generalMeanRows 485).error (generalMeanGrid j.val)+
      (generalMeanRows 485).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 485).c)).2-
      (generalMeanRows 485).J/2-(generalMeanRows 485).error 4 := by
  have he : (generalMeanRows 485).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 485) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 485)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0485

/-! Kernel-checked entropy margins for general spectral rectangle 486. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0486
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7656128634, 7438439272, 7229530763, 7028937091, 6836224340, 6650987814, 6472849481, 6301455706, 6136475219, 5977597307, 5824530185, 5676999535, 5534747177, 5397529882, 5265118280, 5137295881, 5013858172, 4894611800, 4779373819, 4667971006, 4560239229, 4456022865, 4355174264, 4257553261, 4163026714, 4071468085, 3982757045, 3896779117, 3813425332, 3732591921, 3654180016, 3578095384, 3504248166, 3432552644, 3362927017, 3295293189, 3229576580, 3165705939, 3103613170, 3043233177, 2984503704, 2927365198, 2871760673, 2817635581, 2764937695, 2713616994, 2663625558, 2614917467, 2567448705, 2521177071, 2476062093, 2432064950, 2389148390, 2347276664, 2306415454, 2266531808, 2227594078, 2189571865, 2152435957, 2116158283, 2080711856, 2046070733, 2012209960, 1979105539, 1946734378, 1915074259, 1884103794, 1853802395, 1824150239, 1795128231, 1766717982, 1738901771, 1711662521, 1684983774, 1658849662, 1633244884, 1608154685, 1583564829, 1559461583, 1535831693, 1512662366, 1489941254, 1467656430, 1445796378, 1424349973, 1403306465, 1382655469, 1362386944, 1342491185, 1322958806, 1303780732, 1284948183, 1266452664, 1248285956, 1230440103, 1212907402, 1195680396, 1178751861, 1162114803, 1145762441, 1129688208, 1113885736, 1098348855, 1083071578, 1068048102, 1053272797, 1038740200, 1024445011, 1010382084, 996546425, 982933183, 969537649, 956355247, 943381532, 930612183, 918043003, 905669908, 893488931, 881496210, 869687991, 858060621]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 486).prefactor = (2477639399230941/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 486).cutoff/(generalMeanRows 486).c)).2 =
    (179326291033569/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 486).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 486).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 486).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 486

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 486).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 486).criticalRate j.val*(generalMeanRows 486).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 486).c*(generalMeanRows 486).criticalPoint j.val)).2-
      (generalMeanRows 486).J/2-(generalMeanRows 486).error (generalMeanGrid j.val)+
      (generalMeanRows 486).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 486).c)).2-
      (generalMeanRows 486).J/2-(generalMeanRows 486).error 4 := by
  have he : (generalMeanRows 486).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 486) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 486)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0486

/-! Kernel-checked entropy margins for general spectral rectangle 487. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0487
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7034614483, 6808373825, 6591416297, 6383253397, 6183430143, 5991522054, 5807132491, 5629890284, 5459447614, 5295478126, 5137675224, 4985750549, 4839432593, 4698465457, 4562607716, 4431631392, 4305321015, 4183472772, 4065893719, 3952401068, 3842821529, 3736990704, 3634752526, 3535958750, 3440468476, 3348147705, 3258868936, 3172510786, 3088957639, 3008099316, 2929830775, 2854051823, 2780666851, 2709584591, 2640717878, 2573983435, 2509301672, 2446596493, 2385795117, 2326827910, 2269628228, 2214132264, 2160278915, 2108009641, 2057268349, 2008001270, 1960156847, 1913685638, 1868540205, 1824675032, 1782046429, 1740612448, 1700332807, 1661168814, 1623083293, 1586040515, 1550006141, 1514947151, 1480831793, 1447629526, 1415310964, 1383847832, 1353212914, 1323380010, 1294323890, 1266020259, 1238445710, 1211577695, 1185394481, 1159875124, 1134999432, 1110747936, 1087101860, 1064043092, 1041554159, 1019618202, 998218947, 977340689, 956968262, 937087023, 917682830, 898742020, 880251396, 862198202, 844570113, 827355212, 810541981, 794119279, 778076333, 762402723, 747088366, 732123506, 717498703, 703204819, 689233006, 675574698, 662221599, 649165676, 636399144, 623914463, 611704324, 599761644, 588079559, 576651413, 565470750, 554531313, 543827031, 533352013, 523100545, 513067084, 503246246, 493632809, 484221700, 475007994, 465986911, 457153805, 448504164, 440033605, 431737868, 423612813, 415654416]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 487).prefactor = (650671885713237/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 487).cutoff/(generalMeanRows 487).c)).2 =
    (281319378663969/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 487).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 487).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 487).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 487

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 487).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 487).criticalRate j.val*(generalMeanRows 487).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 487).c*(generalMeanRows 487).criticalPoint j.val)).2-
      (generalMeanRows 487).J/2-(generalMeanRows 487).error (generalMeanGrid j.val)+
      (generalMeanRows 487).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 487).c)).2-
      (generalMeanRows 487).J/2-(generalMeanRows 487).error 4 := by
  have he : (generalMeanRows 487).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 487) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 487)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0487

/-! Kernel-checked entropy margins for general spectral rectangle 488. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0488
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7107027051, 6899927324, 6701342409, 6510813896, 6327915002, 6152247761, 5983440522, 5821145736, 5665037964, 5514812098, 5370181765, 5230877884, 5096647359, 4967251908, 4842466981, 4722080792, 4605893430, 4493716041, 4385370087, 4280686665, 4179505878, 4081676256, 3987054227, 3895503623, 3806895228, 3721106354, 3638020455, 3557526759, 3479519938, 3403899789, 3330570945, 3259442603, 3190428269, 3123445518, 3058415778, 2995264116, 2933919046, 2874312346, 2816378886, 2760056467, 2705285670, 2652009713, 2600174318, 2549727583, 2500619864, 2452803664, 2406233524, 2360865928, 2316659203, 2273573432, 2231570374, 2190613376, 2150667304, 2111698469, 2073674559, 2036564577, 2000338777, 1964968609, 1930426663, 1896686616, 1863723186, 1831512082, 1800029962, 1769254386, 1739163783, 1709737407, 1680955303, 1652798271, 1625247837, 1598286217, 1571896287, 1546061559, 1520766151, 1495994762, 1471732645, 1447965589, 1424679889, 1401862333, 1379500175, 1357581119, 1336093300, 1315025265, 1294365958, 1274104702, 1254231185, 1234735447, 1215607859, 1196839119, 1178420232, 1160342500, 1142597514, 1125177134, 1108073488, 1091278955, 1074786158, 1058587954, 1042677426, 1027047873, 1011692801, 996605918, 981781123, 967212504, 952894323, 938821017, 924987189, 911387599, 898017162, 884870943, 871944146, 859232114, 846730325, 834434381, 822340010, 810443057, 798739484, 787225362, 775896870, 764750288, 753781999, 742988480, 732366300]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 488).prefactor = (4893791124759253/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 488).cutoff/(generalMeanRows 488).c)).2 =
    (369092144802517/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 488).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 488).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 488).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 488

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 488).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 488).criticalRate j.val*(generalMeanRows 488).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 488).c*(generalMeanRows 488).criticalPoint j.val)).2-
      (generalMeanRows 488).J/2-(generalMeanRows 488).error (generalMeanGrid j.val)+
      (generalMeanRows 488).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 488).c)).2-
      (generalMeanRows 488).J/2-(generalMeanRows 488).error 4 := by
  have he : (generalMeanRows 488).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 488) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 488)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0488

/-! Kernel-checked entropy margins for general spectral rectangle 489. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0489
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6184503647, 5972887295, 5770240874, 5576085981, 5389976994, 5211498157, 5040261001, 4875902042, 4718080722, 4566477570, 4420792544, 4280743539, 4146065039, 4016506895, 3891833216, 3771821359, 3656261011, 3544953346, 3437710257, 3334353645, 3234714778, 3138633687, 3045958619, 2956545528, 2870257604, 2786964839, 2706543622, 2628876367, 2553851163, 2481361449, 2411305715, 2343587218, 2278113720, 2214797243, 2153553837, 2094303368, 2036969314, 1981478576, 1927761302, 1875750719, 1825382977, 1776597000, 1729334349, 1683539089, 1639157670, 1596138805, 1554433364, 1513994268, 1474776394, 1436736480, 1399833038, 1364026271, 1329277994, 1295551562, 1262811796, 1231024919, 1200158491, 1170181349, 1141063552, 1112776324, 1085292003, 1058583993, 1032626718, 1007395577, 982866899, 959017909, 935826685, 913272123, 891333904, 869992456, 849228932, 829025168, 809363666, 790227558, 771600585, 753467071, 735811896, 718620481, 701878758, 685573154, 669690573, 654218370, 639144342, 624456704, 610144075, 596195462, 582600247, 569348168, 556429311, 543834090, 531553240, 519577805, 507899121, 496508809, 485398764, 474561146, 463988366, 453673080, 443608180, 433786785, 424202230, 414848064, 405718035, 396806089, 388106361, 379613166, 371320994, 363224507, 355318528, 347598036, 340058166, 332694197, 325501549, 318475781, 311612583, 304907771, 298357287, 291957190, 285703654, 279592966, 273621518]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 489).prefactor = (1021478587168889/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 489).cutoff/(generalMeanRows 489).c)).2 =
    (3373897808911/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 489).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 489).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 489).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 489

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 489).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 489).criticalRate j.val*(generalMeanRows 489).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 489).c*(generalMeanRows 489).criticalPoint j.val)).2-
      (generalMeanRows 489).J/2-(generalMeanRows 489).error (generalMeanGrid j.val)+
      (generalMeanRows 489).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 489).c)).2-
      (generalMeanRows 489).J/2-(generalMeanRows 489).error 4 := by
  have he : (generalMeanRows 489).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 489) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 489)
    prefactorDomain slopePositive criticalMargin finalMargin

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
