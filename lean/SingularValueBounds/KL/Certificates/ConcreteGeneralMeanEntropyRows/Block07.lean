import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 490. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0490
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6490518452, 6297264631, 6112113847, 5934622274, 5764376856, 5600992594, 5444110134, 5293393619, 5148528760, 5009221112, 4875194516, 4746189699, 4621962998, 4502285216, 4386940569, 4275725735, 4168448983, 4064929377, 3964996046, 3868487514, 3775251084, 3685142272, 3598024282, 3513767527, 3432249176, 3353352744, 3276967708, 3202989150, 3131317423, 3061857848, 2994520424, 2929219559, 2865873821, 2804405707, 2744741420, 2686810670, 2630546477, 2575884996, 2522765347, 2471129457, 2420921914, 2372089822, 2324582677, 2278352238, 2233352414, 2189539153, 2146870339, 2105305696, 2064806694, 2025336465, 1986859717, 1949342663, 1912752940, 1877059547, 1842232776, 1808244150, 1775066364, 1742673233, 1711039634, 1680141462, 1649955576, 1620459762, 1591632682, 1563453841, 1535903545, 1508962864, 1482613599, 1456838249, 1431619980, 1406942594, 1382790503, 1359148699, 1336002732, 1313338682, 1291143140, 1269403182, 1248106353, 1227240640, 1206794459, 1186756636, 1167116387, 1147863303, 1128987336, 1110478782, 1092328266, 1074526731, 1057065424, 1039935883, 1023129925, 1006639635, 990457358, 974575682, 958987436, 943685676, 928663676, 913914922, 899433101, 885212095, 871245974, 857528985, 844055552, 830820262, 817817863, 805043258, 792491499, 780157779, 768037430, 756125917, 744418832, 732911890, 721600926, 710481889, 699550837, 688803939, 678237462, 667847774, 657631341, 647584718, 637704552, 627987577, 618430607]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 490).prefactor = (1189917262019187/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 490).cutoff/(generalMeanRows 490).c)).2 =
    (191706099288633/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 490).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 490).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 490).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 490

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 490).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 490).criticalRate j.val*(generalMeanRows 490).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 490).c*(generalMeanRows 490).criticalPoint j.val)).2-
      (generalMeanRows 490).J/2-(generalMeanRows 490).error (generalMeanGrid j.val)+
      (generalMeanRows 490).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 490).c)).2-
      (generalMeanRows 490).J/2-(generalMeanRows 490).error 4 := by
  have he : (generalMeanRows 490).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 490) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 490)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0490

/-! Kernel-checked entropy margins for general spectral rectangle 491. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0491
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6115197797, 5929783039, 5752227969, 5582098211, 5418989607, 5262525567, 5112354707, 4968148734, 4829600566, 4696422627, 4568345324, 4445115667, 4326496016, 4212262952, 4102206243, 3996127905, 3893841345, 3795170575, 3699949491, 3608021217, 3519237491, 3433458111, 3350550416, 3270388810, 3192854318, 3117834182, 3045221481, 2974914775, 2906817783, 2840839077, 2776891798, 2714893394, 2654765372, 2596433066, 2539825426, 2484874814, 2431516815, 2379690064, 2329336076, 2280399094, 2232825940, 2186565882, 2141570503, 2097793579, 2055190966, 2013720494, 1973341865, 1934016554, 1895707727, 1858380148, 1822000105, 1786535331, 1751954934, 1718229330, 1685330176, 1653230316, 1621903716, 1591325417, 1561471480, 1532318939, 1503845751, 1476030762, 1448853656, 1422294920, 1396335807, 1370958302, 1346145085, 1321879501, 1298145534, 1274927769, 1252211376, 1229982075, 1208226116, 1186930256, 1166081734, 1145668253, 1125677957, 1106099414, 1086921597, 1068133867, 1049725955, 1031687950, 1014010281, 996683700, 979699277, 963048379, 946722659, 930714050, 915014746, 899617195, 884514090, 869698358, 855163149, 840901830, 826907973, 813175352, 799697929, 786469854, 773485450, 760739211, 748225797, 735940022, 723876854, 712031405, 700398929, 688974816, 677754584, 666733878, 655908464, 645274224, 634827155, 624563360, 614479049, 604570530, 594834212, 585266596, 575864277, 566623934, 557542335, 548616327, 539842838]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 491).prefactor = (583991030703803/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 491).cutoff/(generalMeanRows 491).c)).2 =
    (15501663676771/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 491).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 491).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 491).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 491

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 491).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 491).criticalRate j.val*(generalMeanRows 491).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 491).c*(generalMeanRows 491).criticalPoint j.val)).2-
      (generalMeanRows 491).J/2-(generalMeanRows 491).error (generalMeanGrid j.val)+
      (generalMeanRows 491).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 491).c)).2-
      (generalMeanRows 491).J/2-(generalMeanRows 491).error 4 := by
  have he : (generalMeanRows 491).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 491) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 491)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0491

/-! Kernel-checked entropy margins for general spectral rectangle 492. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0492
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5450915802, 5262543048, 5082383209, 4909985988, 4744932201, 4586831047, 4435317677, 4290051032, 4150711894, 4017001148, 3888638207, 3765359596, 3646917666, 3533079431, 3423625507, 3318349147, 3217055359, 3119560100, 3025689536, 2935279363, 2848174183, 2764226929, 2683298334, 2605256444, 2529976159, 2457338818, 2387231809, 2319548206, 2254186432, 2191049951, 2130046971, 2071090176, 2014096474, 1958986756, 1905685676, 1854121448, 1804225645, 1755933023, 1709181350, 1663911243, 1620066018, 1577591554, 1536436154, 1496550423, 1457887151, 1420401200, 1384049402, 1348790459, 1314584851, 1281394747, 1249183923, 1217917686, 1187562795, 1158087397, 1129460954, 1101654188, 1074639016, 1048388496, 1022876775, 998079036, 973971451, 950531138, 927736114, 905565257, 883998269, 863015633, 842598584, 822729074, 803389737, 784563867, 766235379, 748388791, 731009194, 714082227, 697594055, 681531344, 665881247, 650631373, 635769777, 621284936, 607165736, 593401451, 579981728, 566896575, 554136343, 541691713, 529553683, 517713556, 506162928, 494893675, 483897942, 473168135, 462696909, 452477158, 442502007, 432764803, 423259105, 413978679, 404917488, 396069684, 387429603, 378991758, 370750832, 362701669, 354839274, 347158802, 339655557, 332324980, 325162653, 318164287, 311325721, 304642914, 298111947, 291729012, 285490413, 279392560, 273431965, 267605241, 261909095, 256340328, 250895831]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 492).prefactor = (1209123154356143/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 492).cutoff/(generalMeanRows 492).c)).2 =
    (156409022861669/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 492).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 492).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 492).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 492

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 492).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 492).criticalRate j.val*(generalMeanRows 492).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 492).c*(generalMeanRows 492).criticalPoint j.val)).2-
      (generalMeanRows 492).J/2-(generalMeanRows 492).error (generalMeanGrid j.val)+
      (generalMeanRows 492).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 492).c)).2-
      (generalMeanRows 492).J/2-(generalMeanRows 492).error 4 := by
  have he : (generalMeanRows 492).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 492) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 492)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0492

/-! Kernel-checked entropy margins for general spectral rectangle 493. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0493
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5293387489, 5112960344, 4940437115, 4775379538, 4617379810, 4466057922, 4321059282, 4182052602, 4048727988, 3920795241, 3797982309, 3680033899, 3566710218, 3457785829, 3353048607, 3252298795, 3155348134, 3062019068, 2972144025, 2885564738, 2802131641, 2721703296, 2644145876, 2569332679, 2497143686, 2427465142, 2360189181, 2295213464, 2232440851, 2171779094, 2113140549, 2056441913, 2001603970, 1948551362, 1897212372, 1847518718, 1799405367, 1752810354, 1707674614, 1663941828, 1621558278, 1580472702, 1540636171, 1502001965, 1464525456, 1428164003, 1392876850, 1358625027, 1325371264, 1293079903, 1261716819, 1231249343, 1201646190, 1172877393, 1144914237, 1117729202, 1091295901, 1065589029, 1040584309, 1016258447, 992589085, 969554755, 947134840, 925309533, 904059802, 883367355, 863214603, 843584632, 824461171, 805828564, 787671741, 769976195, 752727957, 735913571, 719520071, 703534963, 687946203, 672742178, 657911687, 643443925, 629328468, 615555251, 602114561, 588997016, 576193556, 563695429, 551494175, 539581618, 527949856, 516591245, 505498392, 494664145, 484081585, 473744014, 463644947, 453778105, 444137409, 434716967, 425511073, 416514196, 407720974, 399126210, 390724863, 382512046, 374483016, 366633173, 358958050, 351453314, 344114758, 336938295, 329919957, 323055892, 316342354, 309775704, 303352408, 297069027, 290922221, 284908741, 279025425, 273269203, 267637083]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 493).prefactor = (4723505828352781/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 493).cutoff/(generalMeanRows 493).c)).2 =
    (67553338217461/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 493).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 493).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 493).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 493

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 493).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 493).criticalRate j.val*(generalMeanRows 493).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 493).c*(generalMeanRows 493).criticalPoint j.val)).2-
      (generalMeanRows 493).J/2-(generalMeanRows 493).error (generalMeanGrid j.val)+
      (generalMeanRows 493).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 493).c)).2-
      (generalMeanRows 493).J/2-(generalMeanRows 493).error 4 := by
  have he : (generalMeanRows 493).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 493) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 493)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0493

/-! Kernel-checked entropy margins for general spectral rectangle 494. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0494
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5188359274, 5015892087, 4850995101, 4693243140, 4542240810, 4397619897, 4259037052, 4126171708, 3998724228, 3876414229, 3758979070, 3646172493, 3537763384, 3433534650, 3333282199, 3236814008, 3143949270, 3054517617, 2968358403, 2885320051, 2805259446, 2728041381, 2653538044, 2581628545, 2512198474, 2445139501, 2380348996, 2317729680, 2257189303, 2198640341, 2141999716, 2087188534, 2034131840, 1982758394, 1933000454, 1884793581, 1838076452, 1792790686, 1748880679, 1706293455, 1664978521, 1624887734, 1585975170, 1548197012, 1511511435, 1475878500, 1441260060, 1407619662, 1374922464, 1343135147, 1312225846, 1282164067, 1252920625, 1224467576, 1196778155, 1169826719, 1143588693, 1118040515, 1093159589, 1068924239, 1045313663, 1022307894, 999887758, 978034839, 956731441, 935960559, 915705842, 895951566, 876682605, 857884403, 839542949, 821644754, 804176824, 787126644, 770482149, 754231712, 738364121, 722868561, 707734600, 692952166, 678511542, 664403341, 650618498, 637148255, 623984149, 611117999, 598541893, 586248183, 574229465, 562478580, 550988595, 539752799, 528764694, 518017984, 507506573, 497224548, 487166183, 477325921, 467698378, 458278327, 449060701, 440040581, 431213190, 422573895, 414118193, 405841713, 397740207, 389809548, 382045727, 374444844, 367003108, 359716835, 352582439, 345596433, 338755423, 332056108, 325495275, 319069793, 312776619, 306612784, 300575400]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 494).prefactor = (575363324326491/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 494).cutoff/(generalMeanRows 494).c)).2 =
    (73716897525883/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 494).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 494).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 494).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 494

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 494).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 494).criticalRate j.val*(generalMeanRows 494).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 494).c*(generalMeanRows 494).criticalPoint j.val)).2-
      (generalMeanRows 494).J/2-(generalMeanRows 494).error (generalMeanGrid j.val)+
      (generalMeanRows 494).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 494).c)).2-
      (generalMeanRows 494).J/2-(generalMeanRows 494).error 4 := by
  have he : (generalMeanRows 494).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 494) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 494)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0494

/-! Kernel-checked entropy margins for general spectral rectangle 495. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0495
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5289388681, 5118390151, 4954906622, 4798511335, 4648807621, 4505426276, 4368023215, 4236277378, 4109888844, 3988577140, 3872079716, 3760150560, 3652558949, 3549088310, 3449535187, 3353708293, 3261427651, 3172523803, 3086837082, 3004216953, 2924521396, 2847616345, 2773375168, 2701678183, 2632412222, 2565470209, 2500750790, 2438157971, 2377600795, 2318993034, 2262252905, 2207302808, 2154069075, 2102481744, 2052474343, 2003983689, 1956949700, 1911315220, 1867025855, 1824029819, 1782277789, 1741722771, 1702319970, 1664026675, 1626802146, 1590607504, 1555405639, 1521161112, 1487840071, 1455410163, 1423840463, 1393101396, 1363164670, 1334003210, 1305591097, 1277903511, 1250916673, 1224607798, 1198955043, 1173937460, 1149534956, 1125728248, 1102498827, 1079828919, 1057701451, 1036100018, 1015008850, 994412786, 974297241, 954648183, 935452106, 916696009, 898367367, 880454116, 862944629, 845827697, 829092513, 812728648, 796726043, 781074987, 765766104, 750790338, 736138942, 721803461, 707775722, 694047822, 680612118, 667461214, 654587953, 641985405, 629646860, 617565821, 605735988, 594151262, 582805724, 571693639, 560809443, 550147739, 539703288, 529471005, 519445956, 509623345, 499998516, 490566945, 481324235, 472266112, 463388421, 454687122, 446158282, 437798079, 429602791, 421568797, 413692569, 405970676, 398399774, 390976605, 383697997, 376560857, 369562173, 362699007, 355968494]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 495).prefactor = (2300093559175257/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 495).cutoff/(generalMeanRows 495).c)).2 =
    (197849889810369/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 495).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 495).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 495).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 495

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 495).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 495).criticalRate j.val*(generalMeanRows 495).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 495).c*(generalMeanRows 495).criticalPoint j.val)).2-
      (generalMeanRows 495).J/2-(generalMeanRows 495).error (generalMeanGrid j.val)+
      (generalMeanRows 495).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 495).c)).2-
      (generalMeanRows 495).J/2-(generalMeanRows 495).error 4 := by
  have he : (generalMeanRows 495).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 495) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 495)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0495

/-! Kernel-checked entropy margins for general spectral rectangle 496. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0496
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5018310668, 4846453557, 4682256620, 4525286331, 4375139621, 4231441228, 4093841316, 3962013363, 3835652254, 3714472568, 3598207037, 3486605147, 3379431873, 3276466527, 3177501714, 3082342377, 2990804922, 2902716422, 2817913881, 2736243567, 2657560386, 2581727318, 2508614889, 2438100685, 2370068902, 2304409934, 2241019983, 2179800704, 2120658872, 2063506074, 2008258421, 1954836280, 1903164025, 1853169803, 1804785319, 1757945630, 1712588957, 1668656507, 1626092305, 1584843040, 1544857918, 1506088524, 1468488696, 1432014400, 1396623620, 1362276248, 1328933986, 1296560254, 1265120092, 1234580086, 1204908285, 1176074124, 1148048359, 1120802995, 1094311231, 1068547393, 1043486882, 1019106123, 995382513, 972294373, 949820906, 927942152, 906638953, 885892910, 865686349, 846002289, 826824407, 808137010, 789925006, 772173875, 754869644, 737998862, 721548579, 705506321, 689860068, 674598238, 659709667, 645183587, 631009613, 617177725, 603678255, 590501867, 577639547, 565082591, 552822585, 540851403, 529161188, 517744342, 506593518, 495701610, 485061740, 474667253, 464511704, 454588855, 444892662, 435417271, 426157009, 417106379, 408260049, 399612852, 391159775, 382895955, 374816675, 366917356, 359193553, 351640952, 344255362, 337032714, 329969054, 323060541, 316303442, 309694129, 303229073, 296904847, 290718113, 284665628, 278744236, 272950865, 267282527, 261736314, 256309394]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 496).prefactor = (4667567841579483/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 496).cutoff/(generalMeanRows 496).c)).2 =
    (91142215256391/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 496).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 496).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 496).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 496

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 496).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 496).criticalRate j.val*(generalMeanRows 496).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 496).c*(generalMeanRows 496).criticalPoint j.val)).2-
      (generalMeanRows 496).J/2-(generalMeanRows 496).error (generalMeanGrid j.val)+
      (generalMeanRows 496).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 496).c)).2-
      (generalMeanRows 496).J/2-(generalMeanRows 496).error 4 := by
  have he : (generalMeanRows 496).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 496) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 496)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0496

/-! Kernel-checked entropy margins for general spectral rectangle 497. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0497
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5384044737, 5214776186, 5052876879, 4897928738, 4749543182, 4607358544, 4471037779, 4340266402, 4214750647, 4094215806, 3978404731, 3867076480, 3760005091, 3656978468, 3557797362, 3462274453, 3370233495, 3281508550, 3195943273, 3113390263, 3033710460, 2956772596, 2882452685, 2810633550, 2741204391, 2674060379, 2609102285, 2546236133, 2485372878, 2426428108, 2369321763, 2313977879, 2260324343, 2208292672, 2157817798, 2108837874, 2061294090, 2015130502, 1970293867, 1926733496, 1884401112, 1843250717, 1803238468, 1764322557, 1726463108, 1689622066, 1653763108, 1618851544, 1584854237, 1551739520, 1519477118, 1488038080, 1457394711, 1427520502, 1398390079, 1369979139, 1342264402, 1315223555, 1288835207, 1263078845, 1237934788, 1213384150, 1189408799, 1165991323, 1143114994, 1120763736, 1098922096, 1077575213, 1056708791, 1036309072, 1016362815, 996857267, 977780145, 959119613, 940864263, 923003094, 905525497, 888421235, 871680428, 855293539, 839251355, 823544978, 808165808, 793105533, 778356115, 763909779, 749759003, 735896507, 722315243, 709008386, 695969326, 683191655, 670669165, 658395836, 646365832, 634573490, 623013315, 611679974, 600568292, 589673242, 578989939, 568513641, 558239738, 548163748, 538281315, 528588201, 519080286, 509753558, 500604116, 491628161, 482821994, 474182015, 465704715, 457386677, 449224570, 441215150, 433355252, 425641792, 418071762, 410642228, 403350327]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 497).prefactor = (4540320064896447/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 497).cutoff/(generalMeanRows 497).c)).2 =
    (406249990515891/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 497).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 497).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 497).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 497

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 497).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 497).criticalRate j.val*(generalMeanRows 497).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 497).c*(generalMeanRows 497).criticalPoint j.val)).2-
      (generalMeanRows 497).J/2-(generalMeanRows 497).error (generalMeanGrid j.val)+
      (generalMeanRows 497).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 497).c)).2-
      (generalMeanRows 497).J/2-(generalMeanRows 497).error 4 := by
  have he : (generalMeanRows 497).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 497) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 497)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0497

/-! Kernel-checked entropy margins for general spectral rectangle 498. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0498
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5107588769, 4937223163, 4774373284, 4618614518, 4469552100, 4326818505, 4190071124, 4058990186, 3933276890, 3812651729, 3696852979, 3585635322, 3478768614, 3376036754, 3277236657, 3182177322, 3090678974, 3002572283, 2917697646, 2835904526, 2757050850, 2681002448, 2607632535, 2536821242, 2468455172, 2402426991, 2338635055, 2276983057, 2217379701, 2159738403, 2103977003, 2050017512, 1997785860, 1947211670, 1898228048, 1850771378, 1804781144, 1760199749, 1716972354, 1675046729, 1634373104, 1594904039, 1556594294, 1519400716, 1483282124, 1448199204, 1414114413, 1380991885, 1348797344, 1317498023, 1287062585, 1257461051, 1228664733, 1200646165, 1173379047, 1146838181, 1120999423, 1095839628, 1071336600, 1047469050, 1024216548, 1001559486, 979479036, 957957112, 936976342, 916520025, 896572107, 877117150, 858140300, 839627264, 821564286, 803938118, 786736000, 769945638, 753555186, 737553221, 721928730, 706671087, 691770041, 677215698, 662998506, 649109239, 635538986, 622279138, 609321372, 596657641, 584280167, 572181422, 560354125, 548791228, 537485909, 526431561, 515621787, 505050387, 494711355, 484598868, 474707283, 465031125, 455565085, 446304013, 437242910, 428376924, 419701347, 411211604, 402903253, 394771980, 386813592, 379024014, 371399285, 363935556, 356629080, 349476217, 342473423, 335617253, 328904350, 322331452, 315895379, 309593037, 303421413, 297377571, 291458655]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 498).prefactor = (4606754062629121/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 498).cutoff/(generalMeanRows 498).c)).2 =
    (187559535960359/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 498).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 498).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 498).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 498

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 498).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 498).criticalRate j.val*(generalMeanRows 498).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 498).c*(generalMeanRows 498).criticalPoint j.val)).2-
      (generalMeanRows 498).J/2-(generalMeanRows 498).error (generalMeanGrid j.val)+
      (generalMeanRows 498).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 498).c)).2-
      (generalMeanRows 498).J/2-(generalMeanRows 498).error 4 := by
  have he : (generalMeanRows 498).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 498) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 498)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0498

/-! Kernel-checked entropy margins for general spectral rectangle 499. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0499
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5118049295, 4949592462, 4788597853, 4634639645, 4487322132, 4346277085, 4211161419, 4081655081, 3957459178, 3838294272, 3723898857, 3614027968, 3508451934, 3406955234, 3309335459, 3215402366, 3124977014, 3037890971, 2953985589, 2873111334, 2795127176, 2719900022, 2647304195, 2577220956, 2509538051, 2444149310, 2380954255, 2319857754, 2260769686, 2203604640, 2148281629, 2094723823, 2042858308, 1992615849, 1943930682, 1896740307, 1850985308, 1806609169, 1763558117, 1721780967, 1681228974, 1641855704, 1603616902, 1566470376, 1530375887, 1495295040, 1461191188, 1428029341, 1395776074, 1364399450, 1333868939, 1304155348, 1275230752, 1247068427, 1219642792, 1192929348, 1166904628, 1141546145, 1116832338, 1092742535, 1069256903, 1046356411, 1024022788, 1002238490, 980986663, 960251114, 940016274, 920267172, 900989411, 882169133, 863793002, 845848176, 828322287, 811203419, 794480085, 778141212, 762176122, 746574512, 731326440, 716422311, 701852856, 687609126, 673682473, 660064538, 646747242, 633722770, 620983565, 608522312, 596331934, 584405577, 572736606, 561318590, 550145303, 539210708, 528508951, 518034359, 507781428, 497744817, 487919344, 478299980, 468881841, 459660186, 450630407, 441788030, 433128706, 424648207, 416342424, 408207360, 400239129, 392433951, 384788146, 377298133, 369960428, 362771638, 355728460, 348827675, 342066149, 335440829, 328948738, 322586978, 316352721]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 499).prefactor = (4600978192214141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 499).cutoff/(generalMeanRows 499).c)).2 =
    (49280014170937/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 499).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 499).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 499).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 499

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 499).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 499).criticalRate j.val*(generalMeanRows 499).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 499).c*(generalMeanRows 499).criticalPoint j.val)).2-
      (generalMeanRows 499).J/2-(generalMeanRows 499).error (generalMeanGrid j.val)+
      (generalMeanRows 499).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 499).c)).2-
      (generalMeanRows 499).J/2-(generalMeanRows 499).error 4 := by
  have he : (generalMeanRows 499).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 499) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 499)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0499

/-! Kernel-checked entropy margins for general spectral rectangle 500. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0500
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5257120816, 5089166386, 4928630950, 4775088235, 4628142249, 4487424638, 4352592326, 4223325399, 4099325215, 3980312690, 3866026761, 3756222994, 3650672316, 3549159869, 3451483967, 3357455136, 3266895250, 3179636726, 3095521799, 3014401843, 2936136760, 2860594403, 2787650059, 2717185958, 2649090829, 2583259481, 2519592423, 2457995505, 2398379587, 2340660232, 2284757422, 2230595286, 2178101858, 2127208843, 2077851402, 2029967948, 1983499960, 1938391808, 1894590586, 1852045959, 1810710017, 1770537142, 1731483881, 1693508822, 1656572491, 1620637238, 1585667147, 1551627934, 1518486868, 1486212685, 1454775511, 1424146791, 1394299218, 1365206672, 1336844155, 1309187737, 1282214502, 1255902494, 1230230672, 1205178863, 1180727719, 1156858678, 1133553923, 1110796349, 1088569525, 1066857667, 1045645600, 1024918736, 1004663043, 984865018, 965511667, 946590474, 928089389, 909996797, 892301505, 874992720, 858060033, 841493400, 825283126, 809419853, 793894541, 778698458, 763823163, 749260497, 735002570, 721041750, 707370651, 693982124, 680869247, 668025316, 655443837, 643118515, 631043249, 619212122, 607619395, 596259503, 585127041, 574216765, 563523582, 553042546, 542768853, 532697832, 522824947, 513145784, 503656053, 494351581, 485228308, 476282282, 467509659, 458906693, 450469739, 442195247, 434079758, 426119901, 418312392, 410654028, 403141690, 395772333, 388542988, 381450761, 374492826]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 500).prefactor = (919599295651671/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 500).cutoff/(generalMeanRows 500).c)).2 =
    (103892083656339/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 500).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 500).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 500).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 500

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 500).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 500).criticalRate j.val*(generalMeanRows 500).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 500).c*(generalMeanRows 500).criticalPoint j.val)).2-
      (generalMeanRows 500).J/2-(generalMeanRows 500).error (generalMeanGrid j.val)+
      (generalMeanRows 500).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 500).c)).2-
      (generalMeanRows 500).J/2-(generalMeanRows 500).error 4 := by
  have he : (generalMeanRows 500).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 500) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 500)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0500

/-! Kernel-checked entropy margins for general spectral rectangle 501. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0501
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5203807617, 5035005212, 4873683237, 4719412399, 4571793868, 4430456626, 4295055088, 4165266974, 4040791409, 3921347199, 3806671285, 3696517338, 3590654491, 3488866182, 3390949104, 3296712244, 3205976006, 3118571410, 3034339357, 2953129949, 2874801871, 2799221815, 2726263956, 2655809461, 2587746040, 2521967528, 2458373499, 2396868905, 2337363748, 2279772764, 2224015142, 2170014251, 2117697394, 2066995571, 2017843267, 1970178245, 1923941361, 1879076379, 1835529817, 1793250779, 1752190821, 1712303806, 1673545782, 1635874859, 1599251099, 1563636408, 1528994437, 1495290491, 1462491438, 1430565631, 1399482823, 1369214102, 1339731817, 1311009514, 1283021876, 1255744662, 1229154659, 1203229623, 1177948236, 1153290058, 1129235484, 1105765702, 1082862658, 1060509013, 1038688118, 1017383970, 996581191, 976264992, 956421150, 937035979, 918096304, 899589442, 881503175, 863825731, 846545765, 829652336, 813134895, 796983261, 781187610, 765738459, 750626646, 735843324, 721379942, 707228234, 693380209, 679828135, 666564534, 653582166, 640874024, 628433321, 616253484, 604328143, 592651126, 581216446, 570018300, 559051059, 548309260, 537787602, 527480937, 517384270, 507492747, 497801652, 488306404, 479002549, 469885758, 460951822, 452196644, 443616243, 435206741, 426964366, 418885447, 410966407, 403203764, 395594127, 388134192, 380820739, 373650630, 366620806, 359728286, 352970161, 346343595]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 501).prefactor = (1157468839524963/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 501).cutoff/(generalMeanRows 501).c)).2 =
    (81551158977713/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 501).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 501).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 501).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 501

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 501).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 501).criticalRate j.val*(generalMeanRows 501).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 501).c*(generalMeanRows 501).criticalPoint j.val)).2-
      (generalMeanRows 501).J/2-(generalMeanRows 501).error (generalMeanGrid j.val)+
      (generalMeanRows 501).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 501).c)).2-
      (generalMeanRows 501).J/2-(generalMeanRows 501).error 4 := by
  have he : (generalMeanRows 501).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 501) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 501)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0501

/-! Kernel-checked entropy margins for general spectral rectangle 502. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0502
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5154124145, 4984479935, 4822350546, 4667307156, 4518951267, 4376912057, 4240844020, 4110424850, 3985353545, 3865348699, 3750146961, 3639501642, 3533181450, 3430969344, 3332661491, 3238066305, 3147003585, 3059303712, 2974806918, 2893362616, 2814828783, 2739071386, 2665963864, 2595386638, 2527226668, 2461377030, 2397736541, 2336209398, 2276704845, 2219136868, 2163423909, 2109488599, 2057257506, 2006660911, 1957632584, 1910109585, 1864032079, 1819343152, 1775988653, 1733917034, 1693079209, 1653428414, 1614920083, 1577511728, 1541162825, 1505834709, 1471490474, 1438094884, 1405614278, 1374016494, 1343270787, 1313347759, 1284219286, 1255858457, 1228239510, 1201337776, 1175129620, 1149592395, 1124704392, 1100444791, 1076793619, 1053731711, 1031240668, 1009302822, 987901202, 967019497, 946642030, 926753726, 907340084, 888387150, 869881494, 851810183, 834160762, 816921231, 800080021, 783625983, 767548362, 751836783, 736481235, 721472053, 706799904, 692455777, 678430961, 664717039, 651305875, 638189600, 625360602, 612811515, 600535212, 588524792, 576773571, 565275075, 554023033, 543011364, 532234176, 521685753, 511360553, 501253198, 491358470, 481671304, 472186781, 462900126, 453806701, 444901997, 436181637, 427641363, 419277036, 411084632, 403060237, 395200043, 387500346, 379957539, 372568114, 365328654, 358235831, 351286406, 344477221, 337805202, 331267352, 324860750, 318582551]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 502).prefactor = (926681687721603/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 502).cutoff/(generalMeanRows 502).c)).2 =
    (49280014170937/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 502).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 502).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 502).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 502

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 502).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 502).criticalRate j.val*(generalMeanRows 502).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 502).c*(generalMeanRows 502).criticalPoint j.val)).2-
      (generalMeanRows 502).J/2-(generalMeanRows 502).error (generalMeanGrid j.val)+
      (generalMeanRows 502).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 502).c)).2-
      (generalMeanRows 502).J/2-(generalMeanRows 502).error 4 := by
  have he : (generalMeanRows 502).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 502) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 502)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0502

/-! Kernel-checked entropy margins for general spectral rectangle 503. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0503
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5018987948, 4848977454, 4686552680, 4531281489, 4382762244, 4240621149, 4104509876, 3974103434, 3849098267, 3729210535, 3614174566, 3503741451, 3397677782, 3295764489, 3197795796, 3103578258, 3012929888, 2925679357, 2841665252, 2760735408, 2682746282, 2607562385, 2535055751, 2465105450, 2397597140, 2332422646, 2269479580, 2208670974, 2149904953, 2093094424, 2038156787, 1985013670, 1933590674, 1883817145, 1835625954, 1788953293, 1743738487, 1699923818, 1657454353, 1616277792, 1576344325, 1537606489, 1500019043, 1463538849, 1428124754, 1393737489, 1360339567, 1327895187, 1296370147, 1265731765, 1235948791, 1206991342, 1178830830, 1151439892, 1124792335, 1098863073, 1073628071, 1049064298, 1025149672, 1001863018, 979184022, 957093190, 935571806, 914601900, 894166210, 874248147, 854831766, 835901737, 817443313, 799442306, 781885061, 764758430, 748049754, 731746836, 715837923, 700311684, 685157197, 670363926, 655921704, 641820722, 628051510, 614604922, 601472125, 588644586, 576114055, 563872561, 551912391, 540226090, 528806441, 517646462, 506739394, 496078693, 485658020, 475471235, 465512389, 455775716, 446255624, 436946694, 427843668, 418941446, 410235078, 401719762, 393390835, 385243769, 377274167, 369477759, 361850394, 354388040, 347086779, 339942798, 332952395, 326111966, 319418006, 312867106, 306455948, 300181304, 294040032, 288029073, 282145446, 276386252, 270748665]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 503).prefactor = (4666067271367059/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 503).cutoff/(generalMeanRows 503).c)).2 =
    (378914142889271/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 503).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 503).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 503).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 503

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 503).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 503).criticalRate j.val*(generalMeanRows 503).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 503).c*(generalMeanRows 503).criticalPoint j.val)).2-
      (generalMeanRows 503).J/2-(generalMeanRows 503).error (generalMeanGrid j.val)+
      (generalMeanRows 503).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 503).c)).2-
      (generalMeanRows 503).J/2-(generalMeanRows 503).error 4 := by
  have he : (generalMeanRows 503).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 503) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 503)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0503

/-! Kernel-checked entropy margins for general spectral rectangle 504. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0504
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5299774480, 5132730364, 4972990537, 4820138073, 4673785576, 4533572601, 4399163354, 4270244627, 4146523955, 4027727947, 3913600788, 3803902882, 3698409617, 3596910251, 3499206892, 3405113569, 3314455385, 3227067737, 3142795608, 3061492908, 2983021877, 2907252526, 2834062130, 2763334754, 2694960817, 2628836686, 2564864308, 2502950853, 2443008401, 2384953637, 2328707573, 2274195290, 2221345694, 2170091293, 2120367984, 2072114860, 2025274020, 1979790405, 1935611630, 1892687840, 1850971562, 1810417581, 1770982807, 1732626165, 1695308485, 1658992395, 1623642231, 1589223940, 1555704999, 1523054333, 1491242239, 1460240316, 1430021398, 1400559487, 1371829700, 1343808207, 1316472181, 1289799747, 1263769932, 1238362628, 1213558540, 1189339153, 1165686693, 1142584089, 1120014940, 1097963487, 1076414576, 1055353636, 1034766646, 1014640115, 994961052, 975716950, 956895755, 938485855, 920476051, 902855548, 885613929, 868741142, 852227483, 836063584, 820240394, 804749167, 789581450, 774729071, 760184124, 745938963, 731986185, 718318627, 704929349, 691811632, 678958964, 666365033, 654023721, 641929093, 630075395, 618457041, 607068611, 595904842, 584960624, 574230994, 563711129, 553396342, 543282077, 533363905, 523637517, 514098724, 504743448, 495567720, 486567678, 477739561, 469079706, 460584546, 452250605, 444074495, 436052917, 428182651, 420460561, 412883586, 405448741, 398153116, 390993869]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 504).prefactor = (4539729682131809/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 504).cutoff/(generalMeanRows 504).c)).2 =
    (413036250200249/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 504).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 504).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 504).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 504

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 504).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 504).criticalRate j.val*(generalMeanRows 504).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 504).c*(generalMeanRows 504).criticalPoint j.val)).2-
      (generalMeanRows 504).J/2-(generalMeanRows 504).error (generalMeanGrid j.val)+
      (generalMeanRows 504).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 504).c)).2-
      (generalMeanRows 504).J/2-(generalMeanRows 504).error 4 := by
  have he : (generalMeanRows 504).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 504) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 504)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0504

/-! Kernel-checked entropy margins for general spectral rectangle 505. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0505
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5057858722, 4886640773, 4723033364, 4566604908, 4416954199, 4273707765, 4136517504, 4005058562, 3879027439, 3758140275, 3642131315, 3530751507, 3423767244, 3320959213, 3222121349, 3127059885, 3035592476, 2947547407, 2862762856, 2781086225, 2702373522, 2626488794, 2553303596, 2482696513, 2414552709, 2348763508, 2285226019, 2223842767, 2164521373, 2107174237, 2051718257, 1998074560, 1946168252, 1895928187, 1847286751, 1800179659, 1754545764, 1710326883, 1667467627, 1625915250, 1585619502, 1546532491, 1508608556, 1471804145, 1436077707, 1401389580, 1367701892, 1334978471, 1303184754, 1272287702, 1242255723, 1213058600, 1184667418, 1157054501, 1130193349, 1104058577, 1078625864, 1053871898, 1029774327, 1006311713, 983463488, 961209911, 939532031, 918411645, 897831270, 877774100, 858223985, 839165391, 820583377, 802463570, 784792132, 767555741, 750741570, 734337259, 718330897, 702711004, 687466511, 672586741, 658061393, 643880527, 630034546, 616514185, 603310494, 590414827, 577818827, 565514416, 553493785, 541749380, 530273893, 519060251, 508101611, 497391346, 486923037, 476690469, 466687618, 456908648, 447347900, 437999890, 428859296, 419920960, 411179872, 402631176, 394270155, 386092230, 378092955, 370268012, 362613205, 355124460, 347797813, 340629416, 333615525, 326752499, 320036799, 313464981, 307033695, 300739681, 294579766, 288550862, 282649962, 276874140, 271220543]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 505).prefactor = (4670126918512371/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 505).cutoff/(generalMeanRows 505).c)).2 =
    (373183468180287/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 505).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 505).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 505).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 505

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 505).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 505).criticalRate j.val*(generalMeanRows 505).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 505).c*(generalMeanRows 505).criticalPoint j.val)).2-
      (generalMeanRows 505).J/2-(generalMeanRows 505).error (generalMeanGrid j.val)+
      (generalMeanRows 505).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 505).c)).2-
      (generalMeanRows 505).J/2-(generalMeanRows 505).error 4 := by
  have he : (generalMeanRows 505).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 505) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 505)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0505

/-! Kernel-checked entropy margins for general spectral rectangle 506. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0506
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5299412729, 5132365082, 4972648956, 4819843936, 4673559465, 4533432232, 4399123849, 4270318766, 4146722400, 4028059453, 3914072391, 3804520071, 3699176496, 3597829683, 3500280630, 3406342379, 3315839153, 3228605575, 3144485940, 3063333559, 2985010146, 2909385256, 2836335773, 2765745426, 2697504351, 2631508679, 2567660163, 2505865820, 2446037609, 2388092126, 2331950323, 2277537247, 2224781790, 2173616470, 2123977207, 2075803137, 2029036414, 1983622047, 1939507730, 1896643695, 1854982567, 1814479230, 1775090706, 1736776033, 1699496156, 1663213825, 1627893499, 1593501248, 1560004677, 1527372834, 1495576145, 1464586334, 1434376360, 1404920351, 1376193545, 1348172234, 1320833712, 1294156219, 1268118902, 1242701762, 1217885617, 1193652060, 1169983422, 1146862736, 1124273701, 1102200654, 1080628538, 1059542871, 1038929724, 1018775689, 999067862, 979793813, 960941568, 942499589, 924456751, 906802326, 889525966, 872617682, 856067835, 839867113, 824006523, 808477375, 793271268, 778380079, 763795952, 749511284, 735518719, 721811134, 708381630, 695223525, 682330343, 669695808, 657313833, 645178516, 633284131, 621625120, 610196090, 598991804, 588007174, 577237259, 566677259, 556322505, 546168462, 536210717, 526444978, 516867070, 507472931, 498258605, 489220243, 480354094, 471656508, 463123927, 454752883, 446540000, 438481983, 430575621, 422817784, 415205417, 407735542, 400405250, 393211707]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 506).prefactor = (913598260804973/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 506).cutoff/(generalMeanRows 506).c)).2 =
    (52341783914361/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 506).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 506).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 506).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 506

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 506).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 506).criticalRate j.val*(generalMeanRows 506).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 506).c*(generalMeanRows 506).criticalPoint j.val)).2-
      (generalMeanRows 506).J/2-(generalMeanRows 506).error (generalMeanGrid j.val)+
      (generalMeanRows 506).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 506).c)).2-
      (generalMeanRows 506).J/2-(generalMeanRows 506).error 4 := by
  have he : (generalMeanRows 506).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 506) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 506)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0506

/-! Kernel-checked entropy margins for general spectral rectangle 507. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0507
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5337064508, 5168845045, 5007981264, 4854053306, 4706671050, 4565471516, 4430116544, 4300290726, 4175699536, 4056067660, 3941137486, 3830667728, 3724432196, 3622218665, 3523827850, 3429072472, 3337776403, 3249773882, 3164908801, 3083034043, 3004010878, 2927708402, 2854003027, 2782778002, 2713922975, 2647333586, 2582911088, 2520562001, 2460197784, 2401734538, 2345092718, 2290196878, 2236975424, 2185360389, 2135287220, 2086694579, 2039524160, 1993720514, 1949230891, 1906005082, 1863995283, 1823155957, 1783443714, 1744817189, 1707236936, 1670665321, 1635066427, 1600405964, 1566651179, 1533770777, 1501734849, 1470514792, 1440083248, 1410414039, 1381482105, 1353263449, 1325735082, 1298874976, 1272662012, 1247075938, 1222097324, 1197707526, 1173888644, 1150623486, 1127895538, 1105688927, 1083988395, 1062779266, 1042047423, 1021779279, 1001961751, 982582244, 963628621, 945089185, 926952663, 909208179, 891845245, 874853738, 858223887, 841946256, 826011732, 810411506, 795137067, 780180184, 765532897, 751187504, 737136553, 723372827, 709889341, 696679325, 683736224, 671053680, 658625532, 646445805, 634508703, 622808600, 611340039, 600097720, 589076497, 578271372, 567677487, 557290123, 547104693, 537116735, 527321912, 517716002, 508294901, 499054611, 489991243, 481101010, 472380223, 463825290, 455432709, 447199072, 439121052, 431195410, 423418986, 415788698, 408301541, 400954583, 393744962]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 507).prefactor = (2285835959295439/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 507).cutoff/(generalMeanRows 507).c)).2 =
    (413036250200249/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 507).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 507).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 507).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 507

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 507).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 507).criticalRate j.val*(generalMeanRows 507).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 507).c*(generalMeanRows 507).criticalPoint j.val)).2-
      (generalMeanRows 507).J/2-(generalMeanRows 507).error (generalMeanGrid j.val)+
      (generalMeanRows 507).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 507).c)).2-
      (generalMeanRows 507).J/2-(generalMeanRows 507).error 4 := by
  have he : (generalMeanRows 507).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 507) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 507)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0507

/-! Kernel-checked entropy margins for general spectral rectangle 508. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0508
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5195942645, 5027161494, 4865808352, 4711460220, 4563724003, 4422233897, 4286649063, 4156651539, 4031944369, 3912249918, 3797308356, 3686876278, 3580725464, 3478641742, 3380423964, 3285883056, 3194841171, 3107130893, 3022594521, 2941083406, 2862457340, 2786583998, 2713338420, 2642602531, 2574264701, 2508219337, 2444366503, 2382611567, 2322864879, 2265041462, 2209060736, 2154846248, 2102325436, 2051429391, 2002092652, 1954253002, 1907851285, 1862831229, 1819139287, 1776724478, 1735538254, 1695534355, 1656668692, 1618899225, 1582185852, 1546490308, 1511776062, 1478008230, 1445153486, 1413179982, 1382057269, 1351756227, 1322248996, 1293508911, 1265510443, 1238229141, 1211641578, 1185725301, 1160458783, 1135821374, 1111793265, 1088355441, 1065489646, 1043178344, 1021404690, 1000152491, 979406180, 959150784, 939371899, 920055661, 901188723, 882758233, 864751806, 847157511, 829963843, 813159710, 796734412, 780677625, 764979382, 749630062, 734620372, 719941334, 705584271, 691540796, 677802799, 664362435, 651212114, 638344489, 625752449, 613429107, 601367792, 589562043, 578005593, 566692372, 555616490, 544772238, 534154073, 523756620, 513574658, 503603122, 493837089, 484271780, 474902551, 465724888, 456734405, 447926836, 439298034, 430843963, 422560700, 414444425, 406491421, 398698069, 391060847, 383576324, 376241157, 369052092, 362005957, 355099660, 348330189, 341694605, 335190046]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 508).prefactor = (1150959726384957/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 508).cutoff/(generalMeanRows 508).c)).2 =
    (49698990971597/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 508).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 508).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 508).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 508

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 508).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 508).criticalRate j.val*(generalMeanRows 508).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 508).c*(generalMeanRows 508).criticalPoint j.val)).2-
      (generalMeanRows 508).J/2-(generalMeanRows 508).error (generalMeanGrid j.val)+
      (generalMeanRows 508).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 508).c)).2-
      (generalMeanRows 508).J/2-(generalMeanRows 508).error 4 := by
  have he : (generalMeanRows 508).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 508) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 508)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0508

/-! Kernel-checked entropy margins for general spectral rectangle 509. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0509
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5274423938, 5105910637, 4944854963, 4790827410, 4643429029, 4502288754, 4367061024, 4237423650, 4113075901, 3993736780, 3879143470, 3769049929, 3663225608, 3561454300, 3463533077, 3369271333, 3278489899, 3191020242, 3106703721, 3025390914, 2946940990, 2871221136, 2798106026, 2727477332, 2659223272, 2593238190, 2529422170, 2467680674, 2407924210, 2350068020, 2294031791, 2239739390, 2187118609, 2136100933, 2086621325, 2038618019, 1992032333, 1946808489, 1902893450, 1860236761, 1818790407, 1778508672, 1739348018, 1701266957, 1664225945, 1628187273, 1593114968, 1558974701, 1525733697, 1493360654, 1461825666, 1431100149, 1401156771, 1371969389, 1343512988, 1315763622, 1288698359, 1262295233, 1236533193, 1211392056, 1186852469, 1162895863, 1139504417, 1116661022, 1094349245, 1072553297, 1051258005, 1030448776, 1010111579, 990232910, 970799773, 951799654, 933220500, 915050698, 897279053, 879894773, 862887447, 846247031, 829963830, 814028483, 798431951, 783165498, 768220683, 753589346, 739263594, 725235793, 711498553, 698044724, 684867380, 671959814, 659315529, 646928225, 634791797, 622900325, 611248066, 599829448, 588639063, 577671660, 566922144, 556385561, 546057101, 535932089, 526005981, 516274359, 506732925, 497377501, 488204018, 479208521, 470387155, 461736171, 453251916, 444930831, 436769451, 428764398, 420912380, 413210188, 405654694, 398242847, 390971670, 383838261, 376839786]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 509).prefactor = (289255578779083/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 509).cutoff/(generalMeanRows 509).c)).2 =
    (209231346325861/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 509).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 509).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 509).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 509

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 509).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 509).criticalRate j.val*(generalMeanRows 509).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 509).c*(generalMeanRows 509).criticalPoint j.val)).2-
      (generalMeanRows 509).J/2-(generalMeanRows 509).error (generalMeanGrid j.val)+
      (generalMeanRows 509).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 509).c)).2-
      (generalMeanRows 509).J/2-(generalMeanRows 509).error 4 := by
  have he : (generalMeanRows 509).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 509) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 509)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0509

/-! Kernel-checked entropy margins for general spectral rectangle 510. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0510
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5202567914, 5033791571, 4872508499, 4718287655, 4570728632, 4429458982, 4294131830, 4164423736, 4040032775, 3920676813, 3806091943, 3696031080, 3590262681, 3488569578, 3390747928, 3296606241, 3205964502, 3118653360, 3034513391, 2953394417, 2875154878, 2799661257, 2726787551, 2656414778, 2588430524, 2522728523, 2459208271, 2397774658, 2338337644, 2280811936, 2225116708, 2171175328, 2118915106, 2068267061, 2019165705, 1971548835, 1925357346, 1880535052, 1837028518, 1794786907, 1753761833, 1713907220, 1675179182, 1637535895, 1600937489, 1565345938, 1530724966, 1497039947, 1464257820, 1432347007, 1401277334, 1371019958, 1341547296, 1312832964, 1284851712, 1257579367, 1230992778, 1205069769, 1179789081, 1155130338, 1131073993, 1107601295, 1084694243, 1062335557, 1040508639, 1019197540, 998386931, 978062074, 958208792, 938813444, 919862901, 901344522, 883246130, 865555993, 848262803, 831355659, 814824044, 798657813, 782847174, 767382674, 752255184, 737455883, 722976249, 708808041, 694943294, 681374301, 668093605, 655093990, 642368467, 629910272, 617712849, 605769847, 594075109, 582622667, 571406733, 560421690, 549662091, 539122647, 528798224, 518683836, 508774642, 499065936, 489553147, 480231830, 471097663, 462146447, 453374092, 444776623, 436350170, 428090967, 419995347, 412059740, 404280669, 396654746, 389178672, 381849230, 374663286, 367617785, 360709747, 353936268, 347294512]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 510).prefactor = (928795016590407/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 510).cutoff/(generalMeanRows 510).c)).2 =
    (41065015291493/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 510).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 510).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 510).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 510

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 510).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 510).criticalRate j.val*(generalMeanRows 510).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 510).c*(generalMeanRows 510).criticalPoint j.val)).2-
      (generalMeanRows 510).J/2-(generalMeanRows 510).error (generalMeanGrid j.val)+
      (generalMeanRows 510).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 510).c)).2-
      (generalMeanRows 510).J/2-(generalMeanRows 510).error 4 := by
  have he : (generalMeanRows 510).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 510) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 510)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0510

/-! Kernel-checked entropy margins for general spectral rectangle 511. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0511
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5221816005, 5052429439, 4890549191, 4735744480, 4587615098, 4445788742, 4309918631, 4179681370, 4054775043, 3934917482, 3819844719, 3709309571, 3603080373, 3500939814, 3402683882, 3308120904, 3217070662, 3129363593, 3044840045, 2963349603, 2884750461, 2808908851, 2735698512, 2665000202, 2596701239, 2530695093, 2466880989, 2405163552, 2345452470, 2287662186, 2231711608, 2177523841, 2125025935, 2074148652, 2024826251, 1976996279, 1930599386, 1885579144, 1841881884, 1799456535, 1758254483, 1718229435, 1679337284, 1641535997, 1604785496, 1569047555, 1534285702, 1500465119, 1467552562, 1435516271, 1404325898, 1373952429, 1344368117, 1315546417, 1287461924, 1260090314, 1233408293, 1207393541, 1182024665, 1157281154, 1133143336, 1109592335, 1086610031, 1064179029, 1042282620, 1020904747, 1000029977, 979643472, 959730958, 940278702, 921273485, 902702577, 884553721, 866815102, 849475336, 832523446, 815948844, 799741315, 783891002, 768388387, 753224278, 738389796, 723876362, 709675681, 695779733, 682180760, 668871259, 655843964, 643091844, 630608088, 618386102, 606419492, 594702065, 583227814, 571990916, 560985721, 550206749, 539648679, 529306347, 519174739, 509248985, 499524353, 489996246, 480660194, 471511853, 462547000, 453761524, 445151429, 436712825, 428441926, 420335049, 412388604, 404599098, 396963127, 389477376, 382138614, 374943692, 367889540, 360973168, 354191655, 347542158]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 511).prefactor = (1161474396529789/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 511).cutoff/(generalMeanRows 511).c)).2 =
    (81551158977713/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 511).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 511).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 511).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 511

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 511).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 511).criticalRate j.val*(generalMeanRows 511).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 511).c*(generalMeanRows 511).criticalPoint j.val)).2-
      (generalMeanRows 511).J/2-(generalMeanRows 511).error (generalMeanGrid j.val)+
      (generalMeanRows 511).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 511).c)).2-
      (generalMeanRows 511).J/2-(generalMeanRows 511).error 4 := by
  have he : (generalMeanRows 511).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 511) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 511)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0511

/-! Kernel-checked entropy margins for general spectral rectangle 512. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0512
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5151490671, 4981874692, 4819800667, 4664836228, 4516579662, 4374657240, 4238720825, 4108445734, 3983528820, 3863686745, 3748654418, 3638183588, 3532041565, 3430010056, 3331884107, 3237471142, 3146590076, 3059070512, 2974751995, 2893483339, 2815121996, 2739533483, 2666590849, 2596174186, 2528170173, 2462471661, 2398977279, 2337591074, 2278222179, 2220784501, 2165196427, 2111380563, 2059263473, 2008775452, 1959850306, 1912425145, 1866440197, 1821838625, 1778566364, 1736571963, 1695806439, 1656223140, 1617777616, 1580427500, 1544132393, 1508853756, 1474554816, 1441200466, 1408757179, 1377192926, 1346477093, 1316580416, 1287474902, 1259133771, 1231531388, 1204643212, 1178445734, 1152916430, 1128033710, 1103776873, 1080126063, 1057062225, 1034567072, 1012623043, 991213270, 970321546, 949932290, 930030524, 910601838, 891632369, 873108773, 855018201, 837348278, 820087082, 803223120, 786745315, 770642982, 754905813, 739523860, 724487520, 709787522, 695414909, 681361026, 667617508, 654176268, 641029485, 628169593, 615589271, 603281431, 591239213, 579455971, 567925266, 556640861, 545596710, 534786948, 524205892, 513848025, 503707996, 493780613, 484060833, 474543760, 465224640, 456098854, 447161914, 438409457, 429837242, 421441148, 413217163, 405161387, 397270025, 389539383, 381965868, 374545979, 367276309, 360153540, 353174439, 346335857, 339634725, 333068053, 326632926, 320326502]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 512).prefactor = (2330987630471141/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 512).cutoff/(generalMeanRows 512).c)).2 =
    (400003818084247/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 512).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 512).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 512).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 512

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 512).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 512).criticalRate j.val*(generalMeanRows 512).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 512).c*(generalMeanRows 512).criticalPoint j.val)).2-
      (generalMeanRows 512).J/2-(generalMeanRows 512).error (generalMeanGrid j.val)+
      (generalMeanRows 512).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 512).c)).2-
      (generalMeanRows 512).J/2-(generalMeanRows 512).error 4 := by
  have he : (generalMeanRows 512).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 512) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 512)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0512

/-! Kernel-checked entropy margins for general spectral rectangle 513. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0513
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5132143220, 4963142102, 4801669645, 4647293234, 4499610974, 4358249002, 4222859101, 4093116551, 3968718209, 3849380779, 3734839243, 3624845456, 3519166855, 3417585301, 3319896014, 3225906608, 3135436207, 3048314632, 2964381664, 2883486356, 2805486410, 2730247600, 2657643238, 2587553679, 2519865874, 2454472942, 2391273783, 2330172718, 2271079150, 2213907254, 2158575688, 2105007319, 2053128977, 2002871214, 1954168093, 1906956974, 1861178333, 1816775576, 1773694875, 1731885013, 1691297235, 1651885113, 1613604414, 1576412983, 1540270630, 1505139018, 1470981570, 1437763371, 1405451081, 1374012850, 1343418244, 1313638165, 1284644790, 1256411496, 1228912808, 1202124332, 1176022708, 1150585552, 1125791412, 1101619720, 1078050746, 1055065563, 1032646000, 1010774613, 989434646, 968609999, 948285197, 928445361, 909076179, 890163880, 871695212, 853657412, 836038189, 818825702, 802008536, 785575688, 769516544, 753820868, 738478778, 723480736, 708817532, 694480268, 680460347, 666749459, 653339571, 640222912, 627391965, 614839457, 602558344, 590541810, 578783250, 567276267, 556014662, 544992424, 534203727, 523642920, 513304519, 503183206, 493273817, 483571339, 474070904, 464767786, 455657389, 446735251, 437997034, 429438518, 421055604, 412844302, 404800730, 396921114, 389201779, 381639148, 374229737, 366970157, 359857103, 352887359, 346057790, 339365341, 332807034, 326379968, 320081313]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 513).prefactor = (2329957716601057/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 513).cutoff/(generalMeanRows 513).c)).2 =
    (40289817611061/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 513).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 513).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 513).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 513

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 513).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 513).criticalRate j.val*(generalMeanRows 513).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 513).c*(generalMeanRows 513).criticalPoint j.val)).2-
      (generalMeanRows 513).J/2-(generalMeanRows 513).error (generalMeanGrid j.val)+
      (generalMeanRows 513).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 513).c)).2-
      (generalMeanRows 513).J/2-(generalMeanRows 513).error 4 := by
  have he : (generalMeanRows 513).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 513) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 513)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0513

/-! Kernel-checked entropy margins for general spectral rectangle 514. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0514
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5149759198, 4980177986, 4818151278, 4663244974, 4515055797, 4373208604, 4237353979, 4107166090, 3982340754, 3862593700, 3747659003, 3637287664, 3531246324, 3429316093, 3331291489, 3236979467, 3146198528, 3058777911, 2974556844, 2893383864, 2815116185, 2739619120, 2666765544, 2596435405, 2528515263, 2462897870, 2399481782, 2338170989, 2278874583, 2221506446, 2165984955, 2112232714, 2060176300, 2009746029, 1960875735, 1913502565, 1867566790, 1823011621, 1779783047, 1737829673, 1697102579, 1657555175, 1619143078, 1581823989, 1545557578, 1510305377, 1476030685, 1442698465, 1410275263, 1378729121, 1348029500, 1318147202, 1289054307, 1260724103, 1233131026, 1206250599, 1180059382, 1154534914, 1129655669, 1105401007, 1081751134, 1058687054, 1036190536, 1014244076, 992830860, 971934733, 951540166, 931632231, 912196564, 893219350, 874687288, 856587574, 838907874, 821636304, 804761414, 788272160, 772157894, 756408343, 741013592, 725964069, 711250534, 696864057, 682796013, 669038063, 655582146, 642420464, 629545476, 616949881, 604626613, 592568832, 580769912, 569223432, 557923171, 546863100, 536037371, 525440313, 515066426, 504910372, 494966969, 485231187, 475698143, 466363092, 457221424, 448268661, 439500450, 430912557, 422500869, 414261381, 406190201, 398283538, 390537706, 382949116, 375514273, 368229774, 361092305, 354098638, 347245626, 340530206, 333949388, 327500261, 321179986]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 514).prefactor = (935182099676203/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 514).cutoff/(generalMeanRows 514).c)).2 =
    (40289817611061/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 514).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 514).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 514).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 514

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 514).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 514).criticalRate j.val*(generalMeanRows 514).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 514).c*(generalMeanRows 514).criticalPoint j.val)).2-
      (generalMeanRows 514).J/2-(generalMeanRows 514).error (generalMeanGrid j.val)+
      (generalMeanRows 514).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 514).c)).2-
      (generalMeanRows 514).J/2-(generalMeanRows 514).error 4 := by
  have he : (generalMeanRows 514).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 514) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 514)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0514

/-! Kernel-checked entropy margins for general spectral rectangle 515. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0515
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5082563238, 4912754688, 4750523442, 4595435510, 4447087645, 4305104661, 4169137036, 4038858774, 3913965473, 3794172601, 3679213926, 3568840109, 3462817416, 3360926555, 3262961619, 3168729112, 3078047070, 2990744250, 2906659387, 2825640514, 2747544331, 2672235633, 2599586773, 2529477174, 2461792870, 2396426089, 2333274859, 2272242651, 2213238041, 2156174395, 2100969584, 2047545711, 1995828857, 1945748851, 1897239048, 1850236124, 1804679886, 1760513093, 1717681288, 1676132642, 1635817809, 1596689783, 1558703776, 1521817092, 1485989014, 1451180701, 1417355083, 1384476769, 1352511957, 1321428353, 1291195090, 1261782655, 1233162821, 1205308576, 1178194068, 1151794540, 1126086282, 1101046571, 1076653629, 1052886572, 1029725367, 1007150793, 985144400, 963688469, 942765985, 922360595, 902456583, 883038835, 864092816, 845604542, 827560550, 809947881, 792754053, 775967041, 759575257, 743567527, 727933079, 712661519, 697742820, 683167301, 668925617, 655008742, 641407954, 628114827, 615121214, 602419238, 590001279, 577859967, 565988166, 554378972, 543025697, 531921865, 521061200, 510437623, 500045239, 489878334, 479931365, 470198956, 460675892, 451357109, 442237694, 433312874, 424578017, 416028619, 407660309, 399468835, 391450065, 383599984, 375914684, 368390368, 361023338, 353810001, 346746855, 339830495, 333057605, 326424956, 319929403, 313567884, 307337415, 301235088, 295258070]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 515).prefactor = (935621714889883/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 515).cutoff/(generalMeanRows 515).c)).2 =
    (98077868115273/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 515).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 515).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 515).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 515

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 515).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 515).criticalRate j.val*(generalMeanRows 515).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 515).c*(generalMeanRows 515).criticalPoint j.val)).2-
      (generalMeanRows 515).J/2-(generalMeanRows 515).error (generalMeanGrid j.val)+
      (generalMeanRows 515).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 515).c)).2-
      (generalMeanRows 515).J/2-(generalMeanRows 515).error 4 := by
  have he : (generalMeanRows 515).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 515) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 515)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0515

/-! Kernel-checked entropy margins for general spectral rectangle 516. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0516
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5015004128, 4845038472, 4682685154, 4527508526, 4379103777, 4237094234, 4101128968, 3970880639, 3846043572, 3726332018, 3611478586, 3501232829, 3395359953, 3293639655, 3195865055, 3101841731, 3011386826, 2924328242, 2840503894, 2759761025, 2681955579, 2606951622, 2534620807, 2464841882, 2397500232, 2332487461, 2269700996, 2209043728, 2150423675, 2093753666, 2038951052, 1985937438, 1934638423, 1884983372, 1836905192, 1790340128, 1745227571, 1701509879, 1659132208, 1618042357, 1578190618, 1539529642, 1502014305, 1465601590, 1430250469, 1395921803, 1362578234, 1330184092, 1298705310, 1268109336, 1238365056, 1209442718, 1181313864, 1153951265, 1127328853, 1101421670, 1076205807, 1051658355, 1027757354, 1004481745, 981811330, 959726727, 938209332, 917241280, 896805414, 876885245, 857464929, 838529228, 820063489, 802053613, 784486032, 767347681, 750625982, 734308816, 718384503, 702841788, 687669815, 672858116, 658396590, 644275489, 630485400, 617017236, 603862220, 591011867, 578457981, 566192636, 554208167, 542497160, 531052442, 519867069, 508934322, 498247690, 487800872, 477587758, 467602430, 457839152, 448292362, 438956664, 429826827, 420897774, 412164579, 403622459, 395266772, 387093009, 379096791, 371273864, 363620093, 356131461, 348804062, 341634099, 334617879, 327751810, 321032398, 314456244, 308020038, 301720561, 295554678, 289519336, 283611563, 277828464, 272167219]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 516).prefactor = (4694297719184763/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 516).cutoff/(generalMeanRows 516).c)).2 =
    (384677847606021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 516).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 516).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 516).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 516

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 516).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 516).criticalRate j.val*(generalMeanRows 516).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 516).c*(generalMeanRows 516).criticalPoint j.val)).2-
      (generalMeanRows 516).J/2-(generalMeanRows 516).error (generalMeanGrid j.val)+
      (generalMeanRows 516).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 516).c)).2-
      (generalMeanRows 516).J/2-(generalMeanRows 516).error 4 := by
  have he : (generalMeanRows 516).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 516) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 516)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0516

/-! Kernel-checked entropy margins for general spectral rectangle 517. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0517
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5084359119, 4914525450, 4752255985, 4597118484, 4448711284, 4306660631, 4170618299, 4040259460, 3915280767, 3795398636, 3680347689, 3569879350, 3463760571, 3361772673, 3263710292, 3169380418, 3078601515, 2991202717, 2907023092, 2825910961, 2747723278, 2672325054, 2599588827, 2529394176, 2461627267, 2396180434, 2332951792, 2271844879, 2212768319, 2155635515, 2100364357, 2046876955, 1995099390, 1944961475, 1896396544, 1849341244, 1803735347, 1759521569, 1716645405, 1675054977, 1634700882, 1595536056, 1557515649, 1520596903, 1484739036, 1449903141, 1416052079, 1383150393, 1351164213, 1320061175, 1289810346, 1260382145, 1231748275, 1203881660, 1176756382, 1150347619, 1124631596, 1099585530, 1075187580, 1051416801, 1028253104, 1005677210, 983670611, 962215537, 941294917, 920892349, 900992066, 881578907, 862638289, 844156183, 826119083, 808513987, 791328373, 774550177, 758167770, 742169946, 726545894, 711285189, 696377771, 681813927, 667584283, 653679783, 640091680, 626811519, 613831130, 601142610, 588738318, 576610861, 564753083, 553158058, 541819082, 530729659, 519883496, 509274498, 498896754, 488744536, 478812286, 469094616, 459586298, 450282256, 441177566, 432267445, 423547249, 415012467, 406658717, 398481741, 390477399, 382641666, 374970631, 367460488, 360107535, 352908171, 345858891, 338956284, 332197031, 325577897, 319095736, 312747481, 306530144, 300440816, 294476661]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 517).prefactor = (466402565767897/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 517).cutoff/(generalMeanRows 517).c)).2 =
    (77885093514391/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 517).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 517).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 517).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 517

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 517).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 517).criticalRate j.val*(generalMeanRows 517).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 517).c*(generalMeanRows 517).criticalPoint j.val)).2-
      (generalMeanRows 517).J/2-(generalMeanRows 517).error (generalMeanGrid j.val)+
      (generalMeanRows 517).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 517).c)).2-
      (generalMeanRows 517).J/2-(generalMeanRows 517).error 4 := by
  have he : (generalMeanRows 517).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 517) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 517)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0517

/-! Kernel-checked entropy margins for general spectral rectangle 518. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0518
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5102099214, 4931672970, 4768837323, 4613158524, 4464233508, 4321687219, 4185170215, 4054356534, 3928941772, 3808641353, 3693188976, 3582335197, 3475846154, 3373502405, 3275097869, 3180438864, 3089343219, 3001639474, 2917166134, 2835770991, 2757310499, 2681649199, 2608659184, 2538219614, 2470216256, 2404541068, 2341091812, 2279771688, 2220489002, 2163156852, 2107692845, 2054018818, 2002060592, 1951747738, 1903013357, 1855793875, 1810028851, 1765660805, 1722635040, 1680899497, 1640404599, 1601103121, 1562950056, 1525902494, 1489919515, 1454962071, 1420992898, 1387976413, 1355878628, 1324667068, 1294310689, 1264779808, 1236046030, 1208082185, 1180862262, 1154361355, 1128555606, 1103422150, 1078939071, 1055085353, 1031840834, 1009186169, 987102786, 965572852, 944579237, 924105481, 904135763, 884654868, 865648164, 847101571, 829001537, 811335014, 794089437, 777252699, 760813132, 744759488, 729080922, 713766971, 698807538, 684192878, 669913585, 655960570, 642325056, 628998559, 615972879, 603240087, 590792515, 578622743, 566723591, 555088110, 543709570, 532581454, 521697448, 511051433, 500637480, 490449839, 480482934, 470731358, 461189864, 451853359, 442716901, 433775691, 425025069, 416460508, 408077611, 399872104, 391839833, 383976761, 376278960, 368742613, 361364004, 354139520, 347065644, 340138954, 333356116, 326713888, 320209109, 313838704, 307599674, 301489099, 295504134]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 518).prefactor = (2340149573026179/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 518).cutoff/(generalMeanRows 518).c)).2 =
    (77885093514391/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 518).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 518).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 518).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 518

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 518).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 518).criticalRate j.val*(generalMeanRows 518).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 518).c*(generalMeanRows 518).criticalPoint j.val)).2-
      (generalMeanRows 518).J/2-(generalMeanRows 518).error (generalMeanGrid j.val)+
      (generalMeanRows 518).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 518).c)).2-
      (generalMeanRows 518).J/2-(generalMeanRows 518).error 4 := by
  have he : (generalMeanRows 518).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 518) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 518)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0518

/-! Kernel-checked entropy margins for general spectral rectangle 519. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0519
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5036645194, 4866036588, 4703040389, 4547222940, 4398181191, 4255540031, 4118949906, 3988084683, 3862639737, 3742330229, 3626889553, 3516067925, 3409631115, 3307359282, 3209045925, 3114496922, 3023529643, 2935972157, 2851662483, 2770447920, 2692184422, 2616736022, 2543974302, 2473777910, 2406032099, 2340628317, 2277463811, 2216441274, 2157468509, 2100458116, 2045327204, 1991997124, 1940393218, 1890444581, 1842083849, 1795246989, 1749873114, 1705904301, 1663285424, 1621964001, 1581890045, 1543015925, 1505296243, 1468687708, 1433149024, 1398640782, 1365125362, 1332566840, 1300930893, 1270184721, 1240296968, 1211237645, 1182978061, 1155490760, 1128749455, 1102728971, 1077405190, 1052754999, 1028756240, 1005387662, 982628879, 960460328, 938863230, 917819551, 897311966, 877323829, 857839140, 838842514, 820319151, 802254815, 784635802, 767448919, 750681460, 734321187, 718356304, 702775443, 687567641, 672722326, 658229295, 644078704, 630261051, 616767156, 603588158, 590715490, 578140876, 565856314, 553854068, 542126653, 530666829, 519467588, 508522148, 497823942, 487366608, 477143985, 467150103, 457379175, 447825591, 438483911, 429348860, 420415319, 411678322, 403133048, 394774819, 386599091, 378601451, 370777614, 363123416, 355634809, 348307861, 341138747, 334123751, 327259257, 320541747, 313967800, 307534087, 301237369, 295074491, 289042384, 283138059, 277358603, 271701183]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 519).prefactor = (2341241455345961/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 519).cutoff/(generalMeanRows 519).c)).2 =
    (378914142889271/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 519).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 519).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 519).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 519

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 519).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 519).criticalRate j.val*(generalMeanRows 519).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 519).c*(generalMeanRows 519).criticalPoint j.val)).2-
      (generalMeanRows 519).J/2-(generalMeanRows 519).error (generalMeanGrid j.val)+
      (generalMeanRows 519).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 519).c)).2-
      (generalMeanRows 519).J/2-(generalMeanRows 519).error 4 := by
  have he : (generalMeanRows 519).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 519) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 519)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0519

/-! Kernel-checked entropy margins for general spectral rectangle 520. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0520
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4970847115, 4800106406, 4637013179, 4481132063, 4332058389, 4189415513, 4052852425, 3922041609, 3796677127, 3676472887, 3561161089, 3450490813, 3344226739, 3242147991, 3144047072, 3049728909, 2959009962, 2871717426, 2787688484, 2706769632, 2628816053, 2553691039, 2481265464, 2411417289, 2344031115, 2278997754, 2216213850, 2155581511, 2097007977, 2040405308, 1985690094, 1932783185, 1881609439, 1832097490, 1784179525, 1737791084, 1692870864, 1649360543, 1607204614, 1566350224, 1526747031, 1488347064, 1451104593, 1414976012, 1379919720, 1345896016, 1312866998, 1280796469, 1249649848, 1219394085, 1189997581, 1161430118, 1133662782, 1106667904, 1080418993, 1054890678, 1030058653, 1005899624, 982391259, 959512144, 937241732, 915560311, 894448953, 873889488, 853864457, 834357088, 815351260, 796831472, 778782816, 761190949, 744042068, 727322885, 711020606, 695122905, 679617907, 664494167, 649740648, 635346710, 621302087, 607596873, 594221507, 581166758, 568423713, 555983758, 543838574, 531980117, 520400613, 509092542, 498048632, 487261845, 476725371, 466432619, 456377206, 446552949, 436953859, 427574136, 418408155, 409450464, 400695778, 392138971, 383775070, 375599250, 367606829, 359793262, 352154137, 344685170, 337382199, 330241182, 323258191, 316429409, 309751127, 303219737, 296831734, 290583707, 284472339, 278494403, 272646760, 266926354, 261330212, 255855439, 250499217]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 520).prefactor = (2349478150847379/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 520).cutoff/(generalMeanRows 520).c)).2 =
    (92834587270203/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 520).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 520).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 520).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 520

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 520).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 520).criticalRate j.val*(generalMeanRows 520).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 520).c*(generalMeanRows 520).criticalPoint j.val)).2-
      (generalMeanRows 520).J/2-(generalMeanRows 520).error (generalMeanGrid j.val)+
      (generalMeanRows 520).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 520).c)).2-
      (generalMeanRows 520).J/2-(generalMeanRows 520).error 4 := by
  have he : (generalMeanRows 520).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 520) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 520)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0520

/-! Kernel-checked entropy margins for general spectral rectangle 521. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0521
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5034636521, 4864048426, 4701086214, 4545314464, 4396328533, 4253751863, 4117233591, 3986446404, 3861084610, 3740862410, 3625512330, 3514783810, 3408441923, 3306266204, 3208049597, 3113597481, 3022726791, 2935265203, 2851050396, 2769929369, 2691757814, 2616399537, 2543725929, 2473615469, 2405953272, 2340630669, 2277544817, 2216598332, 2157698959, 2100759257, 2045696311, 1992431455, 1940890028, 1891001134, 1842697423, 1795914889, 1750592673, 1706672890, 1664100457, 1622822940, 1582790401, 1543955267, 1506272195, 1469697954, 1434191309, 1399712916, 1366225220, 1333692358, 1302080077, 1271355641, 1241487759, 1212446509, 1184203266, 1156730637, 1130002399, 1103993442, 1078679709, 1054038148, 1030046660, 1006684056, 983930005, 961765001, 940170320, 919127980, 898620710, 878631914, 859145641, 840146552, 821619897, 803551481, 785927644, 768735237, 751961593, 735594513, 719622238, 704033438, 688817183, 673962935, 659460525, 645300139, 631472303, 617967869, 604778000, 591894158, 579308090, 567011821, 554997634, 543258069, 531785905, 520574156, 509616058, 498905062, 488434825, 478199201, 468192235, 458408156, 448841368, 439486444, 430338122, 421391295, 412641009, 404082453, 395710959, 387521992, 379511151, 371674156, 364006852, 356505199, 349165271, 341983252, 334955430, 328078194, 321348033, 314761531, 308315363, 302006293, 295831173, 289786934, 283870592, 278079239, 272410041]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 521).prefactor = (2348314707539523/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 521).cutoff/(generalMeanRows 521).c)).2 =
    (95447960679221/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 521).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 521).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 521).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 521

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 521).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 521).criticalRate j.val*(generalMeanRows 521).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 521).c*(generalMeanRows 521).criticalPoint j.val)).2-
      (generalMeanRows 521).J/2-(generalMeanRows 521).error (generalMeanGrid j.val)+
      (generalMeanRows 521).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 521).c)).2-
      (generalMeanRows 521).J/2-(generalMeanRows 521).error 4 := by
  have he : (generalMeanRows 521).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 521) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 521)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0521

/-! Kernel-checked entropy margins for general spectral rectangle 522. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0522
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4968510397, 4797794584, 4634739593, 4478908300, 4329894452, 4187319964, 4050832527, 3920103452, 3794825738, 3674712340, 3559494597, 3448920816, 3342754987, 3240775612, 3142774643, 3048556513, 2957937249, 2870743657, 2786812583, 2705990225, 2628131506, 2553099496, 2480764874, 2411005440, 2343705654, 2278756218, 2216053681, 2155500078, 2097002594, 2040473249, 1985828605, 1932989501, 1881880792, 1832431120, 1784572688, 1738241061, 1693374968, 1649916125, 1607809067, 1567000990, 1527441602, 1489082987, 1451879475, 1415787518, 1380765576, 1346774013, 1313774992, 1281732380, 1250611662, 1220379853, 1191005423, 1162458216, 1134709387, 1107731330, 1081497617, 1055982942, 1031163060, 1007014739, 983515707, 960644608, 938380954, 916705087, 895598137, 875041984, 855019224, 835513134, 816507643, 797987296, 779937233, 762343155, 745191302, 728468429, 712161781, 696259073, 680748466, 665618550, 650858327, 636457187, 622404897, 608691584, 595307715, 582244088, 569491817, 557042316, 544887290, 533018719, 521428852, 510110192, 499055486, 488257719, 477710098, 467406051, 457339212, 447503415, 437892688, 428501242, 419323470, 410353933, 401587358, 393018631, 384642790, 376455021, 368450654, 360625152, 352974113, 345493260, 338178441, 331025620, 324030877, 317190402, 310500491, 303957543, 297558058, 291298630, 285175946, 279186785, 273328011, 267596571, 261989497, 256503896, 251136953]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 522).prefactor = (4713016662875283/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 522).cutoff/(generalMeanRows 522).c)).2 =
    (187108024454213/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 522).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 522).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 522).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 522

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 522).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 522).criticalRate j.val*(generalMeanRows 522).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 522).c*(generalMeanRows 522).criticalPoint j.val)).2-
      (generalMeanRows 522).J/2-(generalMeanRows 522).error (generalMeanGrid j.val)+
      (generalMeanRows 522).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 522).c)).2-
      (generalMeanRows 522).J/2-(generalMeanRows 522).error 4 := by
  have he : (generalMeanRows 522).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 522) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 522)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0522

/-! Kernel-checked entropy margins for general spectral rectangle 523. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0523
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4988334997, 4816993607, 4653326603, 4496897084, 4347298955, 4204154249, 4067110720, 3935839700, 3810034174, 3689407045, 3573689570, 3462629946, 3355992026, 3253554156, 3155108109, 3060458126, 2969420022, 2881820383, 2797495820, 2716292288, 2638064461, 2562675151, 2489994776, 2419900870, 2352277624, 2287015471, 2224010687, 2163165038, 2104385438, 2047583635, 1992675928, 1939582888, 1888229108, 1838542972, 1790456428, 1743904788, 1698826534, 1655163140, 1612858903, 1571860784, 1532118263, 1493583201, 1456209708, 1419954024, 1384774400, 1350630998, 1317485781, 1285302425, 1254046228, 1223684022, 1194184098, 1165516132, 1137651108, 1110561260, 1084220003, 1058601877, 1033682491, 1009438468, 985847399, 962887793, 940539032, 918781333, 897595704, 876963908, 856868428, 837292431, 818219739, 799634796, 781522643, 763868886, 746659674, 729881672, 713522040, 697568409, 682008864, 666831916, 652026493, 637581916, 623487883, 609734452, 596312031, 583211355, 570423478, 557939758, 545751846, 533851670, 522231428, 510883575, 499800811, 488976075, 478402534, 468073571, 457982781, 448123961, 438491102, 429078380, 419880152, 410890947, 402105462, 393518551, 385125225, 376920641, 368900102, 361059047, 353393047, 345897803, 338569140, 331403000, 324395442, 317542636, 310840859, 304286491, 297876015, 291606006, 285473138, 279474171, 273605955, 267865425, 262249595, 256755561, 251380495]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 523).prefactor = (2357743823775553/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 523).cutoff/(generalMeanRows 523).c)).2 =
    (92834587270203/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 523).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 523).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 523).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 523

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 523).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 523).criticalRate j.val*(generalMeanRows 523).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 523).c*(generalMeanRows 523).criticalPoint j.val)).2-
      (generalMeanRows 523).J/2-(generalMeanRows 523).error (generalMeanGrid j.val)+
      (generalMeanRows 523).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 523).c)).2-
      (generalMeanRows 523).J/2-(generalMeanRows 523).error 4 := by
  have he : (generalMeanRows 523).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 523) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 523)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0523

/-! Kernel-checked entropy margins for general spectral rectangle 524. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0524
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4923611073, 4752169960, 4588438057, 4431976713, 4282378182, 4139262928, 4002277222, 3871090987, 3745395867, 3624903491, 3509343901, 3398464136, 3292026945, 3189809618, 3091602921, 2997210130, 2906446136, 2819136643, 2735117415, 2654233596, 2576339081, 2501295936, 2428973863, 2359249709, 2292007006, 2227135551, 2164531013, 2104094572, 2045732578, 1989356243, 1934881343, 1882227952, 1831320182, 1782085956, 1734456778, 1688367535, 1643756299, 1600564149, 1558735003, 1518215459, 1478954648, 1440904093, 1404017582, 1368251044, 1333562433, 1299911624, 1267260306, 1235571892, 1204811425, 1174945496, 1145942164, 1117770878, 1090402412, 1063808794, 1037963241, 1012840108, 988414821, 964663835, 941564573, 919095388, 897235513, 875965021, 855264784, 835116433, 815502329, 796405520, 777809716, 759699255, 742059074, 724874686, 708132147, 691818036, 675919432, 660423889, 645319418, 630594463, 616237887, 602238951, 588587295, 575272927, 562286202, 549617812, 537258766, 525200385, 513434281, 501952351, 490746760, 479809936, 469134554, 458713531, 448540012, 438607364, 428909165, 419439200, 410191447, 401160074, 392339430, 383724040, 375308595, 367087949, 359057112, 351211242, 343545646, 336055765, 328737178, 321585593, 314596841, 307766876, 301091767, 294567695, 288190951, 281957930, 275865126, 269909135, 264086643, 258394431, 252829366, 247388401, 242068572, 236866995, 231780862]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 524).prefactor = (4732077152151277/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 524).cutoff/(generalMeanRows 524).c)).2 =
    (181909758333393/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 524).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 524).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 524).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 524

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 524).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 524).criticalRate j.val*(generalMeanRows 524).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 524).c*(generalMeanRows 524).criticalPoint j.val)).2-
      (generalMeanRows 524).J/2-(generalMeanRows 524).error (generalMeanGrid j.val)+
      (generalMeanRows 524).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 524).c)).2-
      (generalMeanRows 524).J/2-(generalMeanRows 524).error 4 := by
  have he : (generalMeanRows 524).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 524) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 524)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0524

/-! Kernel-checked entropy margins for general spectral rectangle 525. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0525
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5080498506, 4910728719, 4748548660, 4593522616, 4445245785, 4303341574, 4167459193, 4037271501, 3912473067, 3792778432, 3677920537, 3567649298, 3461730315, 3359943708, 3262083042, 3167954356, 3077375277, 2990174199, 2906189544, 2825269069, 2747269240, 2672054649, 2599497478, 2529477006, 2461879149, 2396596041, 2333525636, 2272571349, 2213641715, 2156650079, 2101514300, 2048156481, 1996502718, 1946482858, 1898030288, 1851081720, 1805577004, 1761458948, 1718673150, 1677167837, 1636893724, 1597803871, 1559853553, 1523000145, 1487202999, 1452423344, 1418624182, 1385770193, 1353827648, 1322764324, 1292549426, 1263153512, 1234548425, 1206707222, 1179604120, 1153214429, 1127514505, 1102481690, 1078094268, 1054331419, 1031173169, 1008600357, 986594588, 965138203, 944214237, 923806392, 903899001, 884477002, 865525907, 847031777, 828981194, 811361243, 794159483, 777363930, 760963031, 744945654, 729301059, 714018889, 699089147, 684502186, 670248691, 656319663, 642706411, 629400533, 616393908, 603678684, 591247263, 579092298, 567206675, 555583509, 544216131, 533098083, 522223107, 511585141, 501178304, 490996898, 481035394, 471288429, 461750801, 452417457, 443283496, 434344156, 425594813, 417030976, 408648278, 400442479, 392409454, 384545194, 376845800, 369307479, 361926541, 354699396, 347622549, 340692600, 333906236, 327260233, 320751449, 314376826, 308133382, 302018213, 296028489]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 525).prefactor = (1172990116574153/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 525).cutoff/(generalMeanRows 525).c)).2 =
    (197602915243727/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 525).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 525).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 525).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 525

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 525).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 525).criticalRate j.val*(generalMeanRows 525).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 525).c*(generalMeanRows 525).criticalPoint j.val)).2-
      (generalMeanRows 525).J/2-(generalMeanRows 525).error (generalMeanGrid j.val)+
      (generalMeanRows 525).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 525).c)).2-
      (generalMeanRows 525).J/2-(generalMeanRows 525).error 4 := by
  have he : (generalMeanRows 525).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 525) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 525)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0525

/-! Kernel-checked entropy margins for general spectral rectangle 526. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0526
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5012613771, 4842690997, 4680392854, 4525281984, 4376952027, 4235024913, 4099148450, 3968994164, 3844255355, 3724645353, 3609895945, 3499755944, 3393989896, 3292376912, 3194709591, 3100793046, 3010444016, 2923490044, 2839768732, 2759127052, 2681420715, 2606513586, 2534277149, 2464590010, 2397337439, 2332410945, 2269707884, 2209131091, 2150588545, 2093993054, 2039261959, 1986316866, 1935083388, 1885490910, 1837472371, 1790964053, 1745905390, 1702238790, 1659909463, 1618865265, 1579056552, 1540436036, 1502958661, 1466581477, 1431263529, 1396965746, 1363650842, 1331283220, 1299828883, 1269255353, 1239531586, 1210627901, 1182515912, 1155168457, 1128559538, 1102664264, 1077458792, 1052920276, 1029026822, 1005757431, 983091966, 961011104, 939496298, 918529740, 898094325, 878173619, 858751827, 839813762, 821344817, 803330940, 785758607, 768614798, 751886974, 735563057, 719631407, 704080804, 688900430, 674079849, 659608993, 645478146, 631677927, 618199276, 605033444, 592171974, 579606694, 567329702, 555333358, 543610269, 532153283, 520955477, 510010150, 499310811, 488851174, 478625148, 468626829, 458850496, 449290601, 439941763, 430798762, 421856534, 413110163, 404554878, 396186046, 387999168, 379989874, 372153917, 364487172, 356985629, 349645387, 342462657, 335433752, 328555086, 321823169, 315234606, 308786094, 302474417, 296296443, 290249123, 284329489, 278534647, 272861782]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 526).prefactor = (4708065525401441/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 526).cutoff/(generalMeanRows 526).c)).2 =
    (77514441126477/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 526).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 526).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 526).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 526

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 526).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 526).criticalRate j.val*(generalMeanRows 526).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 526).c*(generalMeanRows 526).criticalPoint j.val)).2-
      (generalMeanRows 526).J/2-(generalMeanRows 526).error (generalMeanGrid j.val)+
      (generalMeanRows 526).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 526).c)).2-
      (generalMeanRows 526).J/2-(generalMeanRows 526).error 4 := by
  have he : (generalMeanRows 526).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 526) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 526)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0526

/-! Kernel-checked entropy margins for general spectral rectangle 527. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0527
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5032359139, 4861805297, 4698890136, 4543176502, 4394258181, 4251757197, 4115321407, 3984622338, 3859353258, 3739227428, 3623976532, 3513349256, 3407109995, 3305037682, 3206924722, 3112576019, 3021808084, 2934448224, 2850333792, 2769311503, 2691236802, 2615973285, 2543392160, 2473371757, 2405797064, 2340559308, 2277555563, 2216688384, 2157865469, 2100999346, 2046007082, 1992810008, 1941333467, 1891506579, 1843262019, 1796535811, 1751267137, 1707398154, 1664873830, 1623641782, 1583652132, 1544857365, 1507212202, 1470673476, 1435200019, 1400752555, 1367293596, 1334787351, 1303199633, 1272497778, 1242650564, 1213628137, 1185401940, 1157944649, 1131230107, 1105233269, 1079930144, 1055297743, 1031314029, 1007957872, 985209004, 963047974, 941456116, 920415501, 899908914, 879919810, 860432287, 841431057, 822901415, 804829214, 787200838, 770003178, 753223612, 736849978, 720870557, 705274054, 690049577, 675186621, 660675049, 646505080, 632667269, 619152497, 605951956, 593057133, 580459803, 568152012, 556126069, 544374535, 532890211, 521666130, 510695549, 499971935, 489488964, 479240506, 469220624, 459423559, 449843730, 440475725, 431314293, 422354340, 413590923, 405019242, 396634639, 388432590, 380408700, 372558701, 364878443, 357363896, 350011140, 342816364, 335775863, 328886034, 322143369, 315544457, 309085978, 302764701, 296577480, 290521252, 284593034, 278789922, 273109085]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 527).prefactor = (588817861044857/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 527).cutoff/(generalMeanRows 527).c)).2 =
    (384677847606021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 527).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 527).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 527).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 527

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 527).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 527).criticalRate j.val*(generalMeanRows 527).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 527).c*(generalMeanRows 527).criticalPoint j.val)).2-
      (generalMeanRows 527).J/2-(generalMeanRows 527).error (generalMeanGrid j.val)+
      (generalMeanRows 527).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 527).c)).2-
      (generalMeanRows 527).J/2-(generalMeanRows 527).error 4 := by
  have he : (generalMeanRows 527).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 527) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 527)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0527

/-! Kernel-checked entropy margins for general spectral rectangle 528. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0528
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4965910318, 4795233077, 4632229321, 4476460202, 4327517906, 4185022940, 4048621719, 3917984404, 3792802958, 3672789404, 3557674245, 3447205037, 3341145096, 3239272328, 3141378150, 3047266523, 2956753054, 2869664182, 2785836430, 2705115714, 2627356715, 2552422291, 2480182945, 2410516325, 2343306769, 2278444874, 2215827111, 2155355451, 2096937036, 2040483854, 1985912453, 1933143666, 1882102355, 1832717179, 1784920366, 1738647512, 1693837387, 1650431749, 1608375185, 1567614944, 1528100790, 1489784871, 1452621576, 1416567424, 1381580942, 1347622562, 1314654514, 1282640737, 1251546783, 1221339739, 1191988141, 1163461906, 1135732254, 1108771648, 1082553727, 1057053250, 1032246038, 1008108921, 984619690, 961757049, 939500571, 917830654, 896728485, 876176000, 856155848, 836651357, 817646507, 799125892, 781074699, 763478675, 746324105, 729597785, 713287003, 697379512, 681863513, 666727633, 651960907, 637552762, 623492998, 609771771, 596379580, 583307252, 570545929, 558087050, 545922347, 534043825, 522443755, 511114662, 500049316, 489240721, 478682105, 468366911, 458288793, 448441602, 438819381, 429416358, 420226937, 411245694, 402467369, 393886859, 385499217, 377299637, 369283459, 361446158, 353783338, 346290734, 338964199, 331799707, 324793343, 317941306, 311239896, 304685520, 298274681, 292003980, 285870108, 279869847, 274000067, 268257719, 262639836, 257143530, 251765989]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 528).prefactor = (2363422137925423/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 528).cutoff/(generalMeanRows 528).c)).2 =
    (188551026898781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 528).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 528).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 528).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 528

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 528).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 528).criticalRate j.val*(generalMeanRows 528).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 528).c*(generalMeanRows 528).criticalPoint j.val)).2-
      (generalMeanRows 528).J/2-(generalMeanRows 528).error (generalMeanGrid j.val)+
      (generalMeanRows 528).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 528).c)).2-
      (generalMeanRows 528).J/2-(generalMeanRows 528).error 4 := by
  have he : (generalMeanRows 528).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 528) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 528)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0528

/-! Kernel-checked entropy margins for general spectral rectangle 529. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0529
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5088041962, 4918006721, 4755580138, 4600324906, 4451834761, 4309731774, 4173663929, 4043302963, 3918342417, 3798495891, 3683495460, 3573090250, 3467045138, 3365139576, 3267166523, 3172931462, 3082251506, 2994954586, 2910878693, 2829871195, 2751788199, 2676493970, 2603860393, 2533766473, 2466097877, 2400746511, 2337610124, 2276591940, 2217600324, 2160548464, 2105354077, 2051939137, 2000229623, 1950155278, 1901649391, 1854648587, 1809092638, 1764924283, 1722089054, 1680535122, 1640213151, 1601076153, 1563079365, 1526180123, 1490337746, 1455513435, 1421670165, 1388772593, 1356786972, 1325681059, 1295424045, 1265986473, 1237340174, 1209458197, 1182314748, 1155885131, 1130145693, 1105073774, 1080647651, 1056846500, 1033650346, 1011040023, 988997136, 967504022, 946543717, 926099921, 906156966, 886699789, 867713903, 849185367, 831100764, 813447179, 796212170, 779383752, 762950375, 746900903, 731224599, 715911103, 700950419, 686332900, 672049229, 658090408, 644447743, 631112833, 618077556, 605334056, 592874738, 580692251, 568779480, 557129537, 545735754, 534591669, 523691024, 513027752, 502595973, 492389985, 482404257, 472633423, 463072278, 453715769, 444558990, 435597176, 426825702, 418240071, 409835917, 401608993, 393555173, 385670444, 377950905, 370392758, 362992311, 355745969, 348650236, 341701707, 334897065, 328233084, 321706617, 315314603, 309054058, 302922072, 296915813]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 529).prefactor = (2353412629648601/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 529).cutoff/(generalMeanRows 529).c)).2 =
    (198328078532551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 529).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 529).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 529).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 529

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 529).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 529).criticalRate j.val*(generalMeanRows 529).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 529).c*(generalMeanRows 529).criticalPoint j.val)).2-
      (generalMeanRows 529).J/2-(generalMeanRows 529).error (generalMeanGrid j.val)+
      (generalMeanRows 529).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 529).c)).2-
      (generalMeanRows 529).J/2-(generalMeanRows 529).error 4 := by
  have he : (generalMeanRows 529).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 529) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 529)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0529

/-! Kernel-checked entropy margins for general spectral rectangle 530. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0530
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5096731420, 4926405790, 4763701812, 4608181432, 4459437692, 4317092019, 4180791795, 4050208195, 3925034240, 3804983037, 3689786206, 3579192444, 3472966226, 3370886628, 3272746255, 3178350257, 3087515436, 3000069428, 2915849949, 2834704104, 2756487757, 2681064940, 2608307317, 2538093689, 2470309528, 2404846554, 2341602340, 2280479948, 2221387586, 2164238291, 2108949642, 2055443479, 2003645655, 1953485792, 1904897065, 1857815992, 1812182242, 1767938455, 1725030071, 1683405173, 1643014339, 1603810503, 1565748823, 1528786563, 1492882974, 1457999190, 1424098121, 1391144367, 1359104119, 1327945083, 1297636395, 1268148550, 1239453328, 1211523734, 1184333928, 1157859174, 1132075778, 1106961040, 1082493202, 1058651403, 1035415634, 1012766697, 990686165, 969156344, 948160243, 927681532, 907704519, 888214113, 869195802, 850635622, 832520135, 814836400, 797571957, 780714799, 764253356, 748176475, 732473398, 717133750, 702147516, 687505033, 673196968, 659214308, 645548344, 632190660, 619133121, 606367858, 593887262, 581683969, 569750852, 558081014, 546667772, 535504655, 524585394, 513903911, 503454317, 493230898, 483228116, 473440596, 463863122, 454490634, 445318216, 436341098, 427554643, 418954350, 410535842, 402294869, 394227294, 386329100, 378596377, 371025322, 363612236, 356353519, 349245668, 342285272, 335469009, 328793646, 322256034, 315853104, 309581867, 303439409, 297422891]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 530).prefactor = (1178715917043941/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 530).cutoff/(generalMeanRows 530).c)).2 =
    (198328078532551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 530).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 530).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 530).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 530

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 530).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 530).criticalRate j.val*(generalMeanRows 530).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 530).c*(generalMeanRows 530).criticalPoint j.val)).2-
      (generalMeanRows 530).J/2-(generalMeanRows 530).error (generalMeanGrid j.val)+
      (generalMeanRows 530).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 530).c)).2-
      (generalMeanRows 530).J/2-(generalMeanRows 530).error 4 := by
  have he : (generalMeanRows 530).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 530) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 530)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0530

/-! Kernel-checked entropy margins for general spectral rectangle 531. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0531
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5021209249, 4850995096, 4688418649, 4533041800, 4384457491, 4242287005, 4106177546, 3975800075, 3850847367, 3731032262, 3616086085, 3505757219, 3399809807, 3298022580, 3200187782, 3106110192, 3015606234, 2928503156, 2844638281, 2763858319, 2686018734, 2610983156, 2538622850, 2468816214, 2401448320, 2336410493, 2273599910, 2212919242, 2154276309, 2097583770, 2042758824, 1989722942, 1938401610, 1888724093, 1840623213, 1794035144, 1748899216, 1705157737, 1662755825, 1621641246, 1581764270, 1543077529, 1505535889, 1469096327, 1433717817, 1399361221, 1365989189, 1333566064, 1302057790, 1271431834, 1241657097, 1212703849, 1184543655, 1157149305, 1130494758, 1104555079, 1079306385, 1054725792, 1030791365, 1007482073, 984777743, 962659017, 941107318, 920104807, 899634350, 879679485, 860224389, 841253849, 822753234, 804708467, 787106002, 769932795, 753176287, 736824379, 720865409, 705288141, 690081735, 675235740, 660740071, 646584992, 632761109, 619259346, 606070937, 593187413, 580600586, 568302542, 556285627, 544542435, 533065803, 521848796, 510884700, 500167014, 489689441, 479445879, 469430416, 459637319, 450061031, 440696162, 431537483, 422579921, 413818552, 405248596, 396865414, 388664497, 380641469, 372792075, 365112184, 357597777, 350244949, 343049902, 336008944, 329118482, 322375021, 315775161, 309315591, 302993091, 296804523, 290746834, 284817048, 279012270, 273329677]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 531).prefactor = (4716138773218049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 531).cutoff/(generalMeanRows 531).c)).2 =
    (77514441126477/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 531).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 531).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 531).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 531

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 531).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 531).criticalRate j.val*(generalMeanRows 531).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 531).c*(generalMeanRows 531).criticalPoint j.val)).2-
      (generalMeanRows 531).J/2-(generalMeanRows 531).error (generalMeanGrid j.val)+
      (generalMeanRows 531).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 531).c)).2-
      (generalMeanRows 531).J/2-(generalMeanRows 531).error 4 := by
  have he : (generalMeanRows 531).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 531) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 531)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0531

/-! Kernel-checked entropy margins for general spectral rectangle 532. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0532
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5029819466, 4859313436, 4696458207, 4540814922, 4391975826, 4249561550, 4113218694, 3982617656, 3857450683, 3737430123, 3622286840, 3511768785, 3405639698, 3303677929, 3205675367, 3111436455, 3020777304, 2933524864, 2849516180, 2768597700, 2690624637, 2615460391, 2542976004, 2473049665, 2405566251, 2340416898, 2277498610, 2216713888, 2157970397, 2101180643, 2046261684, 1993134858, 1941725522, 1891962820, 1843779458, 1797111501, 1751898175, 1708081690, 1665607068, 1624421987, 1584476631, 1545723551, 1508117536, 1471615488, 1436176312, 1401760803, 1368331546, 1335852822, 1304290520, 1273612046, 1243786253, 1214783357, 1186574874, 1159133549, 1132433296, 1106449136, 1081157147, 1056534404, 1032558935, 1009209673, 986466409, 964309756, 942721100, 921682575, 901177016, 881187933, 861699475, 842696405, 824164066, 806088357, 788455707, 771253053, 754467811, 738087863, 722101528, 706497547, 691265067, 676393614, 661873088, 647693737, 633846148, 620321233, 607110209, 594204592, 581596182, 569277050, 557239528, 545476200, 533979888, 522743646, 511760750, 501024685, 490529146, 480268019, 470235381, 460425491, 450832782, 441451854, 432277470, 423304548, 414528155, 405943504, 397545946, 389330967, 381294181, 373431328, 365738267, 358210975, 350845538, 343638154, 336585122, 329682844, 322927820, 316316643, 309845996, 303512654, 297313475, 291245398, 285305444, 279490712, 273798374]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 532).prefactor = (472422586479489/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 532).cutoff/(generalMeanRows 532).c)).2 =
    (77514441126477/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 532).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 532).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 532).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 532

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 532).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 532).criticalRate j.val*(generalMeanRows 532).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 532).c*(generalMeanRows 532).criticalPoint j.val)).2-
      (generalMeanRows 532).J/2-(generalMeanRows 532).error (generalMeanGrid j.val)+
      (generalMeanRows 532).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 532).c)).2-
      (generalMeanRows 532).J/2-(generalMeanRows 532).error 4 := by
  have he : (generalMeanRows 532).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 532) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 532)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0532

/-! Kernel-checked entropy margins for general spectral rectangle 533. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0533
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5047084219, 4875992930, 4712578705, 4556401178, 4407051194, 4264148084, 4127337234, 3996287910, 3870691304, 3750258776, 3634720266, 3523822860, 3417329487, 3315017737, 3216678782, 3122116398, 3031146061, 2943594128, 2859297087, 2778100855, 2699860151, 2624437905, 2551704717, 2481538358, 2413823308, 2348450332, 2285316078, 2224322714, 2165377586, 2108392903, 2053285436, 1999976253, 1948390455, 1898456944, 1850108193, 1803280050, 1757911530, 1713944646, 1671324231, 1629997783, 1589915315, 1551029216, 1513294119, 1476666779, 1441105958, 1406572318, 1373028316, 1340438110, 1308767470, 1277983694, 1248055524, 1218953076, 1190647768, 1163112252, 1136320350, 1110247001, 1084868197, 1060160937, 1036103173, 1012673765, 989852435, 967619729, 945956971, 924846232, 904270288, 884212592, 864657241, 845588944, 826992992, 808855239, 791162066, 773900363, 757057507, 740621334, 724580126, 708922586, 693637820, 678715321, 664144954, 649916932, 636021813, 622450473, 609194102, 596244188, 583592499, 571231082, 559152242, 547348536, 535812763, 524537953, 513517358, 502744442, 492212877, 481916529, 471849454, 462005892, 452380257, 442967129, 433761254, 424757532, 415951015, 407336897, 398910515, 390667338, 382602966, 374713123, 366993656, 359440526, 352049808, 344817685, 337740443, 330814474, 324036263, 317402393, 310909536, 304554455, 298333997, 292245091, 286284749, 280450058, 274738181]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 533).prefactor = (189617666969017/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 533).cutoff/(generalMeanRows 533).c)).2 =
    (77514441126477/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 533).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 533).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 533).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 533

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 533).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 533).criticalRate j.val*(generalMeanRows 533).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 533).c*(generalMeanRows 533).criticalPoint j.val)).2-
      (generalMeanRows 533).J/2-(generalMeanRows 533).error (generalMeanGrid j.val)+
      (generalMeanRows 533).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 533).c)).2-
      (generalMeanRows 533).J/2-(generalMeanRows 533).error 4 := by
  have he : (generalMeanRows 533).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 533) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 533)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0533

/-! Kernel-checked entropy margins for general spectral rectangle 534. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0534
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5039784115, 4868958880, 4705791633, 4549843611, 4400707124, 4258002846, 4121377394, 3990501161, 3865066373, 3744785335, 3629388858, 3518624823, 3412256889, 3310063314, 3211835884, 3117378935, 3026508458, 2939051283, 2854844326, 2773733902, 2695575090, 2620231151, 2547572985, 2477478642, 2409832853, 2344526612, 2281456779, 2220525712, 2161640932, 2104714806, 2049664252, 1996410465, 1944878669, 1894997871, 1846700646, 1799922926, 1754603810, 1710685381, 1668112538, 1626832839, 1586796349, 1547955505, 1510264982, 1473681573, 1438164076, 1403673181, 1370171372, 1337622833, 1305993354, 1275250251, 1245362284, 1216299583, 1188033578, 1160536933, 1133783479, 1107748163, 1082406985, 1057736950, 1033716014, 1010323042, 987537762, 965340719, 943713242, 922637403, 902095981, 882072431, 862550849, 843515945, 824953014, 806847906, 789187005, 771957202, 755145872, 738740855, 722730430, 707103301, 691848576, 676955747, 662414680, 648215589, 634349032, 620805886, 607577343, 594654890, 582030298, 569695613, 557643143, 545865447, 534355324, 523105806, 512110147, 501361813, 490854477, 480582008, 470538465, 460718088, 451115294, 441724668, 432540955, 423559060, 414774036, 406181081, 397775534, 389552868, 381508685, 373638713, 365938800, 358404912, 351033127, 343819630, 336760712, 329852767, 323092285, 316475849, 310000139, 303661917, 297458036, 291385428, 285441108, 279622167, 273925771]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 534).prefactor = (29534595760537/6250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 534).cutoff/(generalMeanRows 534).c)).2 =
    (193061989728009/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 534).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 534).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 534).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 534

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 534).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 534).criticalRate j.val*(generalMeanRows 534).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 534).c*(generalMeanRows 534).criticalPoint j.val)).2-
      (generalMeanRows 534).J/2-(generalMeanRows 534).error (generalMeanGrid j.val)+
      (generalMeanRows 534).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 534).c)).2-
      (generalMeanRows 534).J/2-(generalMeanRows 534).error 4 := by
  have he : (generalMeanRows 534).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 534) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 534)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0534

/-! Kernel-checked entropy margins for general spectral rectangle 535. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0535
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4964513507, 4793860623, 4630887302, 4475153845, 4326251668, 4183800583, 4047446377, 3916858646, 3791728845, 3671768538, 3556707819, 3446293876, 3340289699, 3238472898, 3140634636, 3046578640, 2956120317, 2869085928, 2785311841, 2704643836, 2626936479, 2552052529, 2479862404, 2410243684, 2343080646, 2278263845, 2215689712, 2155260196, 2096882415, 2040468350, 1985934543, 1933201828, 1882195075, 1832842952, 1785077706, 1738834949, 1694053474, 1650675065, 1608644334, 1567908561, 1528417541, 1490123452, 1452980720, 1416945896, 1381977544, 1348036129, 1315083918, 1283084887, 1252004624, 1221810251, 1192470341, 1163954846, 1136235023, 1109283367, 1083073554, 1057580376, 1032779686, 1008648348, 985164184, 962305929, 940053186, 918386385, 897286740, 876736214, 856717484, 837213907, 818209485, 799688840, 781637180, 764040278, 746884439, 730156483, 713843716, 697933915, 682415297, 667276509, 652506605, 638095028, 624031594, 610306477, 596910190, 583833576, 571067788, 558604282, 546434800, 534551361, 522946247, 511611995, 500541386, 489727432, 479163372, 468842661, 458758957, 448906122, 439278207, 429869447, 420674253, 411687209, 402903061, 394316712, 385923219, 377717785, 369695752, 361852600, 354183941, 346685510, 339353166, 332182887, 325170763, 318312992, 311605882, 305045839, 298629371, 292353080, 286213662, 280207899, 274332663, 268584907, 262961666, 257460054, 252077259]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 535).prefactor = (4733671595644497/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 535).cutoff/(generalMeanRows 535).c)).2 =
    (189274092823781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 535).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 535).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 535).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 535

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 535).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 535).criticalRate j.val*(generalMeanRows 535).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 535).c*(generalMeanRows 535).criticalPoint j.val)).2-
      (generalMeanRows 535).J/2-(generalMeanRows 535).error (generalMeanGrid j.val)+
      (generalMeanRows 535).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 535).c)).2-
      (generalMeanRows 535).J/2-(generalMeanRows 535).error 4 := by
  have he : (generalMeanRows 535).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 535) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 535)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0535

/-! Kernel-checked entropy margins for general spectral rectangle 536. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0536
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4974495455, 4803523145, 4640237585, 4484199171, 4334999382, 4192258068, 4055621035, 3924757871, 3799360010, 3679138976, 3563824804, 3453164614, 3346921316, 3244872428, 3146809010, 3052534681, 2961864731, 2874625299, 2790652624, 2709792357, 2631898927, 2556834955, 2484470721, 2414683661, 2347357911, 2282383882, 2219657864, 2159081661, 2100562251, 2044011472, 1989345727, 1936485712, 1885356161, 1835885606, 1788006162, 1741653311, 1696765717, 1653285040, 1611155767, 1570325059, 1530742593, 1492360432, 1455132889, 1419016406, 1383969440, 1349952351, 1316927308, 1284858184, 1253710475, 1223451208, 1194048867, 1165473315, 1137695724, 1110688508, 1084425262, 1058880699, 1034030600, 1009851754, 986321915, 963419749, 941124793, 919417413, 898278763, 877690746, 857635982, 838097772, 819060066, 800507433, 782425032, 764798588, 747614361, 730859124, 714520144, 698585152, 683042328, 667880281, 653088027, 638654973, 624570902, 610825953, 597410609, 584315682, 571532297, 559051879, 546866145, 534967087, 523346963, 511998284, 500913809, 490086527, 479509657, 469176631, 459081090, 449216875, 439578018, 430158739, 420953431, 411956661, 403163160, 394567817, 386165673, 377951918, 369921882, 362071031, 354394964, 346889406, 339550205, 332373327, 325354851, 318490967, 311777972, 305212265, 298790343, 292508800, 286364324, 280353690, 274473762, 268721487, 263093891, 257588084, 252201245]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 536).prefactor = (4735016112236691/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 536).cutoff/(generalMeanRows 536).c)).2 =
    (188551026898781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 536).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 536).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 536).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 536

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 536).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 536).criticalRate j.val*(generalMeanRows 536).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 536).c*(generalMeanRows 536).criticalPoint j.val)).2-
      (generalMeanRows 536).J/2-(generalMeanRows 536).error (generalMeanGrid j.val)+
      (generalMeanRows 536).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 536).c)).2-
      (generalMeanRows 536).J/2-(generalMeanRows 536).error 4 := by
  have he : (generalMeanRows 536).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 536) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 536)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0536

/-! Kernel-checked entropy margins for general spectral rectangle 537. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0537
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4983095434, 4811827545, 4648259695, 4491951519, 4342493791, 4199505704, 4062632451, 3931543049, 3805928399, 3685499524, 3569985995, 3459134495, 3352707522, 3250482210, 3152249258, 3057811947, 2966985245, 2879594992, 2795477144, 2714477085, 2636448991, 2561255248, 2488765909, 2418858200, 2351416057, 2286329700, 2223495241, 2162814312, 2104193733, 2047545188, 1992784936, 1939833536, 1888615592, 1839059512, 1791097293, 1744664306, 1699699110, 1656143263, 1613941157, 1573039859, 1533388963, 1494940446, 1457648544, 1421469622, 1386362066, 1352286168, 1319204031, 1287079466, 1255877908, 1225566328, 1196113156, 1167488202, 1139662589, 1112608682, 1086300032, 1060711307, 1035818247, 1011597601, 988027083, 965085323, 942751823, 921006915, 899831720, 879208110, 859118676, 839546688, 820476069, 801891361, 783777700, 766120783, 748906847, 732122644, 715755417, 699792876, 684223182, 669034922, 654217095, 639759089, 625650669, 611881958, 598443422, 585325856, 572520370, 560018376, 547811575, 535891946, 524251733, 512883434, 501779796, 490933796, 480338640, 469987750, 459874756, 449993487, 440337967, 430902403, 421681181, 412668858, 403860154, 395249951, 386833282, 378605327, 370561408, 362696985, 355007647, 347489114, 340137224, 332947939, 325917329, 319041579, 312316978, 305739920, 299306896, 293014494, 286859395, 280838370, 274948276, 269186056, 263548732, 258033406, 252637255]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 537).prefactor = (2371601038105419/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 537).cutoff/(generalMeanRows 537).c)).2 =
    (188551026898781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 537).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 537).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 537).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 537

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 537).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 537).criticalRate j.val*(generalMeanRows 537).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 537).c*(generalMeanRows 537).criticalPoint j.val)).2-
      (generalMeanRows 537).J/2-(generalMeanRows 537).error (generalMeanGrid j.val)+
      (generalMeanRows 537).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 537).c)).2-
      (generalMeanRows 537).J/2-(generalMeanRows 537).error 4 := by
  have he : (generalMeanRows 537).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 537) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 537)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0537

/-! Kernel-checked entropy margins for general spectral rectangle 538. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0538
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4917737011, 4746378362, 4582754296, 4426422720, 4276972770, 4134022092, 3997214408, 3866217341, 3740720464, 3620433540, 3505084933, 3394420180, 3288200684, 3186202532, 3088215423, 2994041680, 2903495357, 2816401415, 2732594969, 2651920598, 2574231704, 2499389932, 2427264622, 2357732317, 2290676297, 2225986150, 2163557382, 2103291045, 2045093397, 1988875584, 1934553349, 1882046753, 1831279920, 1782180802, 1734680952, 1688715316, 1644222043, 1601142300, 1559420101, 1519002149, 1479837689, 1441878364, 1405078085, 1369392910, 1334780927, 1301202141, 1268618382, 1236993197, 1206291769, 1176480827, 1147528567, 1119404577, 1092079765, 1065526295, 1039717517, 1014627915, 990233048, 966509492, 943434799, 920987441, 899146771, 877892976, 857207041, 837070709, 817466446, 798377405, 779787396, 761680855, 744042816, 726858880, 710115194, 693798423, 677895728, 662394744, 647283557, 632550687, 618185068, 604176029, 590513278, 577186885, 564187266, 551505171, 539131668, 527058129, 515276218, 503777881, 492555332, 481601042, 470907731, 460468356, 450276101, 440324371, 430606780, 421117145, 411849477, 402797976, 393957020, 385321160, 376885115, 368643762, 360592136, 352725419, 345038934, 337528147, 330188653, 323016178, 316006571, 309155801, 302459951, 295915217, 289517902, 283264413, 277151257, 271175038, 265332455, 259620295, 254035435, 248574836, 243235541, 238014672, 232909430]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 538).prefactor = (2379808242331093/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 538).cutoff/(generalMeanRows 538).c)).2 =
    (73916644276707/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 538).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 538).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 538).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 538

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 538).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 538).criticalRate j.val*(generalMeanRows 538).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 538).c*(generalMeanRows 538).criticalPoint j.val)).2-
      (generalMeanRows 538).J/2-(generalMeanRows 538).error (generalMeanGrid j.val)+
      (generalMeanRows 538).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 538).c)).2-
      (generalMeanRows 538).J/2-(generalMeanRows 538).error 4 := by
  have he : (generalMeanRows 538).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 538) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 538)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0538

/-! Kernel-checked entropy margins for general spectral rectangle 539. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0539
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4903692746, 4732882058, 4569766754, 4413907979, 4264897838, 4122356698, 3985930775, 3855289984, 3730125994, 3610150497, 3495093628, 3384702543, 3278740137, 3176983865, 3079224678, 2985266052, 2894923096, 2808021741, 2724397991, 2643897238, 2566373633, 2491689503, 2419714817, 2350326691, 2283408930, 2218851605, 2156550660, 2096407549, 2038328897, 1982226186, 1928015464, 1875617071, 1824955387, 1775958592, 1728558452, 1682690104, 1638291870, 1595305076, 1553673877, 1513345109, 1474268131, 1436394693, 1399678802, 1364076602, 1329546257, 1296047846, 1263543257, 1231996096, 1201371595, 1171636529, 1142759134, 1114709033, 1087457168, 1060975727, 1035238090, 1010218761, 985893317, 962238354, 939231438, 916851054, 895076567, 873888176, 853266873, 833194409, 813653258, 794626578, 776098186, 758052522, 740474623, 723350096, 706665090, 690406274, 674560811, 659116340, 644060949, 629383161, 615071912, 601116534, 587506737, 574232593, 561284524, 548653280, 536329931, 524305855, 512572717, 501122468, 489947323, 479039759, 468392499, 457998502, 447850959, 437943277, 428269076, 418822177, 409596596, 400586537, 391786383, 383190691, 374794184, 366591746, 358578417, 350749382, 343099975, 335625663, 328322049, 321184865, 314209966, 307393326, 300731037, 294219299, 287854422, 281632820, 275551005, 269605590, 263793278, 258110864, 252555232, 247123349, 241812265, 236619109, 231541086]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 539).prefactor = (1182365272062147/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 539).cutoff/(generalMeanRows 539).c)).2 =
    (366697216494399/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 539).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 539).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 539).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 539

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 539).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 539).criticalRate j.val*(generalMeanRows 539).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 539).c*(generalMeanRows 539).criticalPoint j.val)).2-
      (generalMeanRows 539).J/2-(generalMeanRows 539).error (generalMeanGrid j.val)+
      (generalMeanRows 539).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 539).c)).2-
      (generalMeanRows 539).J/2-(generalMeanRows 539).error 4 := by
  have he : (generalMeanRows 539).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 539) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 539)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0539

/-! Kernel-checked entropy margins for general spectral rectangle 540. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0540
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4975865566, 4804871024, 4641557030, 4485484835, 4336246692, 4193463155, 4056780659, 3925869365, 3800421219, 3680148206, 3564780779, 3454066428, 3347768393, 3245664490, 3147546041, 3053216900, 2962492562, 2875199346, 2791173651, 2710261266, 2632316737, 2557202789, 2484789788, 2414955243, 2347583350, 2282564568, 2219795225, 2159177155, 2100617355, 2044027678, 1989324533, 1936428615, 1885264654, 1835761172, 1787850270, 1741467413, 1696551242, 1653043396, 1610888336, 1570033192, 1530427615, 1492023633, 1454775529, 1418639710, 1383574599, 1349540523, 1316499612, 1284415708, 1253254267, 1222982284, 1193568206, 1164981861, 1137194386, 1110178162, 1083906747, 1058354824, 1033498139, 1009313451, 985778479, 962871860, 940573102, 918862540, 897721300, 877131257, 857075005, 837535817, 818497617, 799944952, 781862956, 764237329, 747054310, 730300652, 713963598, 698030861, 682490602, 667331409, 652542282, 638112611, 624032160, 610291055, 596879763, 583789080, 571010116, 558534287, 546353293, 534459115, 522843999, 511500446, 500421202, 489599249, 479027793, 468700258, 458610276, 448751680, 439118495, 429704930, 420505374, 411514386, 402726690, 394137170, 385740861, 377532947, 369508752, 361663739, 353993501, 346493760, 339160358, 331989258, 324976536, 318118379, 311411080, 304851034, 298434737, 292158781, 286019849, 280014716, 274140243, 268393375, 262771138, 257270638, 251889054]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 540).prefactor = (4728152829719751/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 540).cutoff/(generalMeanRows 540).c)).2 =
    (23478625639083/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 540).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 540).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 540).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 540

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 540).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 540).criticalRate j.val*(generalMeanRows 540).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 540).c*(generalMeanRows 540).criticalPoint j.val)).2-
      (generalMeanRows 540).J/2-(generalMeanRows 540).error (generalMeanGrid j.val)+
      (generalMeanRows 540).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 540).c)).2-
      (generalMeanRows 540).J/2-(generalMeanRows 540).error 4 := by
  have he : (generalMeanRows 540).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 540) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 540)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0540

/-! Kernel-checked entropy margins for general spectral rectangle 541. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0541
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4984503223, 4813211850, 4649614357, 4493271234, 4343774028, 4200742631, 4063822866, 3932684322, 3807018409, 3686536614, 3570968919, 3460062377, 3353579819, 3251298673, 3153009899, 3058517011, 2967635183, 2880190434, 2796018878, 2714966036, 2636886203, 2561641864, 2489103160, 2419147388, 2351658544, 2286526895, 2223648591, 2162925293, 2104263839, 2047575927, 1992777822, 1939790082, 1888537304, 1838947889, 1790953818, 1744490444, 1699496303, 1655912931, 1613684694, 1572758629, 1533084300, 1494613653, 1457300889, 1421102341, 1385976360, 1351883204, 1318784938, 1286645338, 1255429805, 1225105272, 1195640134, 1167004165, 1139168454, 1112105331, 1085788312, 1060192034, 1035292200, 1011065528, 987489702, 964543319, 942205853, 920457603, 899279664, 878653878, 858562810, 838989704, 819918456, 801333584, 783220200, 765563976, 748351129, 731568389, 715202975, 699242580, 683675345, 668489837, 653675037, 639220317, 625115424, 611350466, 597915893, 584802485, 572001339, 559503852, 547301713, 535386888, 523751610, 512388365, 501289889, 490449149, 479859342, 469513879, 459406382, 449530673, 439880765, 430450859, 421235333, 412228738, 403425788, 394821357, 386410473, 378188310, 370150186, 362291555, 354608002, 347095242, 339749110, 332565562, 325540667, 318670604, 311951662, 305380228, 298952793, 292665942, 286516354, 280500797, 274616126, 268859282, 263227285, 257717236, 252326311]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 541).prefactor = (947272095848599/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 541).cutoff/(generalMeanRows 541).c)).2 =
    (23478625639083/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 541).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 541).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 541).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 541

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 541).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 541).criticalRate j.val*(generalMeanRows 541).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 541).c*(generalMeanRows 541).criticalPoint j.val)).2-
      (generalMeanRows 541).J/2-(generalMeanRows 541).error (generalMeanGrid j.val)+
      (generalMeanRows 541).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 541).c)).2-
      (generalMeanRows 541).J/2-(generalMeanRows 541).error 4 := by
  have he : (generalMeanRows 541).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 541) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 541)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0541

/-! Kernel-checked entropy margins for general spectral rectangle 542. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0542
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4994536889, 4822926817, 4659017697, 4502370115, 4352575689, 4209254355, 4072051958, 3940638085, 3814704130, 3693961544, 3578140257, 3466987259, 3360265303, 3257751730, 3159237404, 3064525732, 2973431778, 2885781441, 2801410712, 2720164983, 2641898418, 2566473368, 2493759836, 2423634982, 2355982661, 2290693001, 2227662010, 2166791210, 2107987299, 2051161837, 1996230949, 1943115058, 1891738627, 1842029923, 1793920795, 1747346470, 1702245355, 1658558862, 1616231235, 1575209394, 1535442782, 1496883234, 1459484839, 1423203821, 1387998425, 1353828804, 1320656924, 1288446464, 1257162727, 1226772556, 1197244253, 1168547508, 1140653323, 1113533946, 1087162814, 1061514485, 1036564590, 1012289773, 988667646, 965676741, 943296464, 921507053, 900289539, 879625706, 859498061, 839889793, 820784746, 802167384, 784022769, 766336528, 749094829, 732284357, 715892290, 699906279, 684314423, 669105252, 654267711, 639791133, 625665234, 611880086, 598426109, 585294051, 572474980, 559960265, 547741567, 535810825, 524160247, 512782296, 501669683, 490815354, 480212482, 469854459, 459734887, 449847567, 440186496, 430745856, 421520008, 412503486, 403690988, 395077376, 386657660, 378427002, 370380705, 362514211, 354823093, 347303054, 339949917, 332759628, 325728244, 318851937, 312126982, 305549761, 299116753, 292824536, 286669780, 280649246, 274759782, 268998319, 263361873, 257847537, 252452480]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 542).prefactor = (1184426201210899/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 542).cutoff/(generalMeanRows 542).c)).2 =
    (187108024454213/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 542).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 542).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 542).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 542

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 542).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 542).criticalRate j.val*(generalMeanRows 542).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 542).c*(generalMeanRows 542).criticalPoint j.val)).2-
      (generalMeanRows 542).J/2-(generalMeanRows 542).error (generalMeanGrid j.val)+
      (generalMeanRows 542).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 542).c)).2-
      (generalMeanRows 542).J/2-(generalMeanRows 542).error 4 := by
  have he : (generalMeanRows 542).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 542) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 542)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0542

/-! Kernel-checked entropy margins for general spectral rectangle 543. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0543
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4920802469, 4749395796, 4585711359, 4429308769, 4279778709, 4136740222, 3999838289, 3868741671, 3743140966, 3622746857, 3507288536, 3396512281, 3290180156, 3188068841, 3089968557, 2995682095, 2905023919, 2817819352, 2733903826, 2653122194, 2575328097, 2500383383, 2428157567, 2358527335, 2291376088, 2226593513, 2164075190, 2103722231, 2045440933, 1989142472, 1934742601, 1882161382, 1831322931, 1782155180, 1734589653, 1688561263, 1644008118, 1600871336, 1559094880, 1518625398, 1479412075, 1441406490, 1404562492, 1368836071, 1334185244, 1300569952, 1267951949, 1236294716, 1205563362, 1175724546, 1146746393, 1118598421, 1091251469, 1064677631, 1038850192, 1013743566, 989333247, 965595749, 942508558, 920050086, 898199625, 876937303, 856244049, 836101550, 816492217, 797399150, 778806110, 760697481, 743058251, 725873974, 709130751, 692815205, 676914456, 661416096, 646308174, 631579173, 617217990, 603213920, 589556636, 576236177, 563242930, 550567613, 538201267, 526135237, 514361161, 502870960, 491656823, 480711201, 470026791, 459596528, 449413579, 439471327, 429763372, 420283511, 411025741, 401984244, 393153385, 384527701, 376101897, 367870840, 359829551, 351973200, 344297102, 336796711, 329467614, 322305527, 315306292, 308465868, 301780333, 295245874, 288858790, 282615479, 276512444, 270546285, 264713692, 259011452, 253436435, 247985600, 242655984, 237444708, 232348968]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 543).prefactor = (4745962890700141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 543).cutoff/(generalMeanRows 543).c)).2 =
    (366697216494399/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 543).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 543).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 543).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 543

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 543).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 543).criticalRate j.val*(generalMeanRows 543).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 543).c*(generalMeanRows 543).criticalPoint j.val)).2-
      (generalMeanRows 543).J/2-(generalMeanRows 543).error (generalMeanGrid j.val)+
      (generalMeanRows 543).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 543).c)).2-
      (generalMeanRows 543).J/2-(generalMeanRows 543).error 4 := by
  have he : (generalMeanRows 543).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 543) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 543)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0543

/-! Kernel-checked entropy margins for general spectral rectangle 544. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0544
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5315920753, 5148355822, 4988172025, 4834944127, 4688277174, 4547803852, 4413182122, 4284093104, 4160239186, 4041342308, 3927142423, 3817396106, 3711875279, 3610366071, 3512667768, 3418591857, 3327961153, 3240609003, 3156378553, 3075122072, 2996700336, 2920982059, 2847843365, 2777167304, 2708843404, 2642767257, 2578840130, 2516968615, 2457064292, 2399043425, 2342826674, 2288338833, 2235508574, 2184268225, 2134553547, 2086303538, 2039460242, 1993968573, 1949776155, 1906833159, 1865092171, 1824508047, 1785037789, 1746640432, 1709276923, 1672910025, 1637504212, 1603025584, 1569441773, 1536721865, 1504836323, 1473756915, 1443456645, 1413909689, 1385091335, 1356977927, 1329546808, 1302776274, 1276645522, 1251134609, 1226224405, 1201896557, 1178133446, 1154918157, 1132234441, 1110066684, 1088399877, 1067219586, 1046511928, 1026263540, 1006461561, 987093603, 968147732, 949612450, 931476669, 913729697, 896361220, 879361283, 862720276, 846428920, 830478249, 814859600, 799564597, 784585142, 769913401, 755541793, 741462982, 727669863, 714155555, 700913392, 687936913, 675219856, 662756146, 650539895, 638565385, 626827069, 615319562, 604037634, 592976206, 582130342, 571495245, 561066254, 550838834, 540808577, 530971192, 521322506, 511858458, 502575091, 493468556, 484535102, 475771076, 467172918, 458737160, 450460420, 442339402, 434370890, 426551750, 418878922, 411349424, 403960342, 396708835]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 544).prefactor = (4610961204339809/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 544).cutoff/(generalMeanRows 544).c)).2 =
    (424464946023869/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 544).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 544).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 544).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 544

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 544).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 544).criticalRate j.val*(generalMeanRows 544).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 544).c*(generalMeanRows 544).criticalPoint j.val)).2-
      (generalMeanRows 544).J/2-(generalMeanRows 544).error (generalMeanGrid j.val)+
      (generalMeanRows 544).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 544).c)).2-
      (generalMeanRows 544).J/2-(generalMeanRows 544).error 4 := by
  have he : (generalMeanRows 544).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 544) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 544)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0544

/-! Kernel-checked entropy margins for general spectral rectangle 545. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0545
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5243509425, 5075660420, 4915228217, 4761786073, 4614937604, 4474314138, 4339572344, 4210392113, 4086474657, 3967540798, 3853329416, 3743596057, 3638111663, 3536661417, 3439043700, 3345069125, 3254559673, 3167347883, 3083276124, 3002195917, 2923967315, 2848458337, 2775544434, 2705108007, 2637037957, 2571229269, 2507582626, 2446004051, 2386404577, 2328699938, 2272810280, 2218659900, 2166176990, 2115293411, 2065944475, 2018068742, 1971607832, 1926506252, 1882711226, 1840172543, 1798842416, 1758675338, 1719627965, 1681658991, 1644729036, 1608800544, 1573837684, 1539806255, 1506673602, 1474408531, 1442981234, 1412363218, 1382527232, 1353447208, 1325098195, 1297456307, 1270498666, 1244203352, 1218549354, 1193516527, 1169085548, 1145237874, 1121955706, 1099221952, 1077020195, 1055334656, 1034150168, 1013452145, 993226555, 973459896, 954139168, 935251851, 916785885, 898729648, 881071935, 863801941, 846909241, 830383776, 814215836, 798396042, 782915338, 767764969, 752936475, 738421675, 724212657, 710301763, 696681585, 683344950, 670284910, 657494736, 644967908, 632698105, 620679200, 608905250, 597370488, 586069323, 574996323, 564146216, 553513884, 543094354, 532882793, 522874506, 513064928, 503449620, 494024266, 484784666, 475726734, 466846493, 458140074, 449603706, 441233720, 433026540, 424978683, 417086756, 409347450, 401757540, 394313884, 387013415, 379853143, 372830151, 365941593]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 545).prefactor = (1156657481611239/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 545).cutoff/(generalMeanRows 545).c)).2 =
    (208356484609779/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 545).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 545).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 545).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 545

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 545).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 545).criticalRate j.val*(generalMeanRows 545).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 545).c*(generalMeanRows 545).criticalPoint j.val)).2-
      (generalMeanRows 545).J/2-(generalMeanRows 545).error (generalMeanGrid j.val)+
      (generalMeanRows 545).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 545).c)).2-
      (generalMeanRows 545).J/2-(generalMeanRows 545).error 4 := by
  have he : (generalMeanRows 545).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 545) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 545)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0545

/-! Kernel-checked entropy margins for general spectral rectangle 546. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0546
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4993155874, 4821567154, 4657685671, 4501071150, 4351314430, 4208034744, 4070877299, 3939511110, 3813627052, 3692936111, 3577167801, 3466068735, 3359401333, 3256942636, 3158483242, 3063826322, 2972786732, 2885190187, 2800872517, 2719678974, 2641463601, 2566088645, 2493424020, 2423346811, 2355740812, 2290496101, 2227508645, 2166679937, 2107916652, 2051130335, 1996237106, 1943157383, 1891815636, 1842140138, 1794062753, 1747518723, 1702446477, 1658787448, 1616485906, 1575488797, 1535745597, 1497208168, 1459830632, 1423569248, 1388382291, 1354229952, 1321074230, 1288878839, 1257609118, 1227231945, 1197715658, 1169029980, 1141145948, 1114035846, 1087673143, 1062032432, 1037089374, 1012820647, 989203895, 966217680, 943841438, 922055435, 900840732, 880179143, 860053198, 840446115, 821341761, 802724628, 784579800, 766892927, 749650200, 732838326, 716444503, 700456403, 684862144, 669650275, 654809758, 640329946, 626200569, 612411716, 598953821, 585817650, 572994282, 560475101, 548251780, 536316272, 524660795, 513277826, 502160083, 491300525, 480692335, 470328913, 460203871, 450311018, 440644358, 431198083, 421966560, 412944330, 404126099, 395506731, 387081247, 378844811, 370792734, 362920461, 355223570, 347697768, 340338884, 333142866, 326105776, 319223788, 312493182, 305910341, 299471748, 293173984, 287013721, 280987721, 275092835, 269325998, 263684224, 258164610, 252764327]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 546).prefactor = (4744582376510151/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 546).cutoff/(generalMeanRows 546).c)).2 =
    (23478625639083/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 546).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 546).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 546).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 546

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 546).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 546).criticalRate j.val*(generalMeanRows 546).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 546).c*(generalMeanRows 546).criticalPoint j.val)).2-
      (generalMeanRows 546).J/2-(generalMeanRows 546).error (generalMeanGrid j.val)+
      (generalMeanRows 546).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 546).c)).2-
      (generalMeanRows 546).J/2-(generalMeanRows 546).error 4 := by
  have he : (generalMeanRows 546).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 546) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 546)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0546

/-! Kernel-checked entropy margins for general spectral rectangle 547. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0547
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4919301452, 4747917105, 4584261251, 4427892647, 4278401199, 4135405246, 3998549139, 3867501066, 3741951109, 3621609487, 3506204978, 3395483484, 3289206738, 3187151120, 3089106588, 2994875696, 2904272701, 2817122742, 2733261093, 2652532465, 2574790379, 2499896580, 2427720493, 2358138731, 2291034633, 2226297835, 2163823880, 2103513845, 2045274009, 1989015531, 1934654158, 1882109950, 1831307026, 1782173327, 1734640390, 1688643144, 1644119717, 1601011250, 1559261731, 1518817835, 1479628776, 1441646164, 1404823878, 1369117942, 1334486408, 1300889249, 1268288255, 1236646940, 1205930451, 1176105479, 1147140186, 1119004124, 1091668167, 1065104441, 1039286266, 1014188090, 989785439, 966054857, 942973863, 920520900, 898675288, 877417187, 856727552, 836588099, 816981264, 797890176, 779298619, 761191004, 743552340, 726368206, 709624725, 693308542, 677406795, 661907100, 646797523, 632066567, 617703145, 603696570, 590036533, 576713088, 563716637, 551037913, 538667971, 526598169, 514820159, 503325874, 492107515, 481157543, 470468667, 460033832, 449846214, 439899209, 430186420, 420701657, 411438924, 402392410, 393556488, 384925702, 376494763, 368258544, 360212072, 352350523, 344669218, 337163614, 329829305, 322662010, 315657575, 308811964, 302121258, 295581648, 289189434, 282941021, 276832911, 270861708, 265024107, 259316893, 253736942, 248281211, 242946742, 237730657, 232630152]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 547).prefactor = (4752818546254019/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 547).cutoff/(generalMeanRows 547).c)).2 =
    (368139177811301/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 547).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 547).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 547).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 547

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 547).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 547).criticalRate j.val*(generalMeanRows 547).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 547).c*(generalMeanRows 547).criticalPoint j.val)).2-
      (generalMeanRows 547).J/2-(generalMeanRows 547).error (generalMeanGrid j.val)+
      (generalMeanRows 547).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 547).c)).2-
      (generalMeanRows 547).J/2-(generalMeanRows 547).error 4 := by
  have he : (generalMeanRows 547).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 547) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 547)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0547

/-! Kernel-checked entropy margins for general spectral rectangle 548. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0548
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4929379704, 4757674260, 4593704511, 4437029303, 4287238604, 4143950792, 4006810232, 3875485106, 3749665471, 3629061508, 3513401937, 3402432593, 3295915125, 3193625824, 3095354546, 3000903737, 2910087539, 2822730970, 2738669174, 2657746735, 2579817039, 2504741692, 2432389982, 2362638381, 2295370086, 2230474591, 2167847295, 2107389137, 2049006252, 1992609659, 1938114966, 1885442095, 1834515030, 1785261576, 1737613140, 1691504520, 1646873716, 1603661744, 1561812470, 1521272448, 1481990773, 1443918943, 1407010724, 1371222029, 1336510804, 1302836918, 1270162061, 1238449647, 1207664727, 1177773900, 1148745236, 1120548201, 1093153582, 1066533424, 1040660966, 1015510578, 991057711, 967278837, 944151403, 921653785, 899765237, 878465854, 857736531, 837558922, 817915408, 798789062, 780163612, 762023420, 744353443, 727139213, 710366806, 694022821, 678094356, 662568981, 647434726, 632680051, 618293836, 604265356, 590584266, 577240589, 564224694, 551527284, 539139382, 527052320, 515257721, 503747492, 492513809, 481549108, 470846074, 460397631, 450196932, 440237351, 430512473, 421016089, 411742182, 402684925, 393838673, 385197954, 376757464, 368512060, 360456754, 352586709, 344897231, 337383767, 330041895, 322867324, 315855888, 309003541, 302306353, 295760505, 289362287, 283108094, 276994421, 271017862, 265175103, 259462924, 253878189, 248417853, 243078947, 237858588, 232753965]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 548).prefactor = (297139710679041/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 548).cutoff/(generalMeanRows 548).c)).2 =
    (366697216494399/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 548).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 548).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 548).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 548

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 548).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 548).criticalRate j.val*(generalMeanRows 548).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 548).c*(generalMeanRows 548).criticalPoint j.val)).2-
      (generalMeanRows 548).J/2-(generalMeanRows 548).error (generalMeanGrid j.val)+
      (generalMeanRows 548).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 548).c)).2-
      (generalMeanRows 548).J/2-(generalMeanRows 548).error 4 := by
  have he : (generalMeanRows 548).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 548) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 548)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0548

/-! Kernel-checked entropy margins for general spectral rectangle 549. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0549
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4937971890, 4765967154, 4601711597, 4444763295, 4294711502, 4151173932, 4013794327, 3882240294, 3756201349, 3635387166, 3519525994, 3408363224, 3301660090, 3199192493, 3100749923, 3006134481, 2915159986, 2827651149, 2743442829, 2662379337, 2584313805, 2509107597, 2436629774, 2366756593, 2299371045, 2234362433, 2171625975, 2111062435, 2052577785, 1996082890, 1941493209, 1888728527, 1837712693, 1788373388, 1740641897, 1694452908, 1649744310, 1606457017, 1564534797, 1523924111, 1484573966, 1446435775, 1409463222, 1373612146, 1338840418, 1305107836, 1272376025, 1240608334, 1209769754, 1179826826, 1150747564, 1122501379, 1095059010, 1068392452, 1042474896, 1017280670, 992785180, 968964858, 945797112, 923260279, 901333578, 879997070, 859231614, 839018834, 819341081, 800181396, 781523481, 763351670, 745650893, 728406657, 711605015, 695232542, 679276312, 663723876, 648563241, 633782848, 619371557, 605318624, 591613688, 578246752, 565208169, 552488627, 540079133, 527971002, 516155844, 504625552, 493372288, 482388475, 471666785, 461200130, 450981650, 441004709, 431262881, 421749943, 412459871, 403386828, 394525156, 385869376, 377414174, 369154397, 361085050, 353201287, 345498407, 337971846, 330617176, 323430100, 316406443, 309542152, 302833290, 296276032, 289866662, 283601567, 277477238, 271490261, 265637318, 259915182, 254320713, 248850859, 243502648, 238273189, 233159669]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 549).prefactor = (4762522270427219/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 549).cutoff/(generalMeanRows 549).c)).2 =
    (366697216494399/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 549).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 549).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 549).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 549

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 549).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 549).criticalRate j.val*(generalMeanRows 549).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 549).c*(generalMeanRows 549).criticalPoint j.val)).2-
      (generalMeanRows 549).J/2-(generalMeanRows 549).error (generalMeanGrid j.val)+
      (generalMeanRows 549).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 549).c)).2-
      (generalMeanRows 549).J/2-(generalMeanRows 549).error 4 := by
  have he : (generalMeanRows 549).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 549) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 549)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0549

/-! Kernel-checked entropy margins for general spectral rectangle 550. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0550
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4927840918, 4756159063, 4592219118, 4435579072, 4285828120, 4142583939, 4005490262, 3874214701, 3748446800, 3627896276, 3512291435, 3401377739, 3294916506, 3192683729, 3094469000, 3000074532, 2909314258, 2822013015, 2738005789, 2657137023, 2579259984, 2504236176, 2431934798, 2362232249, 2295011664, 2230162489, 2167580084, 2107165356, 2048824421, 1992468284, 1938012544, 1885377124, 1834486011, 1785267020, 1737651570, 1691574478, 1646973762, 1603790462, 1561968470, 1521454367, 1482197278, 1444148732, 1407262526, 1371494608, 1336802957, 1303147476, 1270489890, 1238793649, 1208023838, 1178147093, 1149131519, 1120946615, 1093563205, 1066953367, 1041090374, 1015948630, 991503617, 967731841, 944610781, 922118842, 900235308, 878940305, 858214755, 838040341, 818399471, 799275242, 780651412, 762512364, 744843080, 727629116, 710856570, 694512063, 678582713, 663056111, 647920306, 633163777, 618775422, 604744533, 591060784, 577714211, 564695198, 551994466, 539603050, 527512296, 515713841, 504199602, 492961769, 481992789, 471285358, 460832410, 450627107, 440662834, 430933185, 421431958, 412153145, 403090927, 394239667, 385593898, 377148324, 368897807, 360837367, 352962172, 345267533, 337748900, 330401859, 323222123, 316205528, 309348034, 302645713, 296094751, 289691441, 283432181, 277313469, 271331900, 265484165, 259767044, 254177406, 248712205, 243368476, 238143336, 233033977]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 550).prefactor = (2380534506625177/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 550).cutoff/(generalMeanRows 550).c)).2 =
    (368139177811301/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 550).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 550).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 550).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 550

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 550).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 550).criticalRate j.val*(generalMeanRows 550).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 550).c*(generalMeanRows 550).criticalPoint j.val)).2-
      (generalMeanRows 550).J/2-(generalMeanRows 550).error (generalMeanGrid j.val)+
      (generalMeanRows 550).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 550).c)).2-
      (generalMeanRows 550).J/2-(generalMeanRows 550).error 4 := by
  have he : (generalMeanRows 550).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 550) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 550)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0550

/-! Kernel-checked entropy margins for general spectral rectangle 551. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0551
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4936395209, 4764415329, 4600190798, 4443278839, 4293267933, 4149775093, 4012443434, 3880939991, 3754953768, 3634193979, 3518388458, 3407282226, 3300636186, 3198225942, 3099840721, 3005282392, 2914364567, 2826911777, 2742758721, 2661749575, 2583737349, 2508583305, 2436156419, 2366332872, 2298995598, 2234033851, 2171342809, 2110823207, 2052380997, 1995927030, 1941376760, 1888649970, 1837670514, 1788366083, 1740667977, 1694510899, 1649832760, 1606574499, 1564679907, 1524095475, 1484770240, 1446655645, 1409705408, 1373875400, 1339123527, 1305409623, 1272695346, 1240944083, 1210120859, 1180192251, 1151126308, 1122892478, 1095461533, 1068805503, 1042897614, 1017712226, 993224779, 969411737, 946250541, 923719557, 901798036, 880466066, 859704538, 839495104, 819820139, 800662712, 782006553, 763836017, 746136061, 728892215, 712090554, 695717674, 679760672, 664207117, 649045037, 634262893, 619849561, 605794316, 592086812, 578717071, 565675459, 552952679, 540539753, 528428010, 516609074, 505074848, 493817507, 482829486, 472103467, 461632373, 451409355, 441427785, 431681246, 422163526, 412868606, 403790657, 394924032, 386263255, 377803019, 369538181, 361463749, 353574883, 345866886, 338335202, 330975407, 323783207, 316754433, 309885034, 303171079, 296608745, 290194319, 283924194, 277794860, 271802908, 265945022, 260217977, 254618635, 249143947, 243790942, 238556732, 233438504]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 551).prefactor = (74520840661217/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 551).cutoff/(generalMeanRows 551).c)).2 =
    (368139177811301/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 551).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 551).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 551).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 551

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 551).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 551).criticalRate j.val*(generalMeanRows 551).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 551).c*(generalMeanRows 551).criticalPoint j.val)).2-
      (generalMeanRows 551).J/2-(generalMeanRows 551).error (generalMeanGrid j.val)+
      (generalMeanRows 551).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 551).c)).2-
      (generalMeanRows 551).J/2-(generalMeanRows 551).error 4 := by
  have he : (generalMeanRows 551).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 551) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 551)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0551

/-! Kernel-checked entropy margins for general spectral rectangle 552. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0552
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5323564369, 5155766887, 4995374154, 4841958573, 4695123043, 4554498291, 4419740494, 4290529156, 4166565186, 4047569185, 3933279891, 3823452768, 3717858740, 3616283024, 3518524081, 3424392655, 3333710888, 3246311519, 3162037145, 3080739543, 3002279048, 2926523975, 2853350094, 2782640140, 2714283358, 2648175090, 2584216384, 2522313636, 2462378256, 2404326359, 2348078478, 2293559293, 2240697385, 2189425000, 2139677834, 2091394830, 2044517989, 1998992190, 1954765031, 1911786669, 1870009676, 1829388905, 1789881360, 1751446080, 1714044024, 1677637967, 1642192403, 1607673449, 1574048760, 1541287446, 1509359997, 1478238208, 1447895110, 1418304909, 1389442923, 1361285525, 1333810090, 1306994944, 1280819316, 1255263291, 1230307770, 1205934429, 1182125680, 1158864635, 1136135075, 1113921412, 1092208664, 1070982423, 1050228831, 1029934551, 1010086744, 990673045, 971681543, 953100760, 934919629, 917127477, 899714008, 882669286, 865983719, 849648040, 833653302, 817990854, 802652336, 787629661, 772915009, 758500808, 744379735, 730544693, 716988812, 703705434, 690688107, 677930575, 665426771, 653170812, 641156987, 629379754, 617833732, 606513696, 595414570, 584531422, 573859458, 563394018, 553130571, 543064708, 533192142, 523508699, 514010319, 504693046, 495553031, 486586522, 477789865, 469159501, 460691959, 452383856, 444231894, 436232857, 428383607, 420681085, 413122302, 405704346, 398424371]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 552).prefactor = (4632009897500649/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 552).cutoff/(generalMeanRows 552).c)).2 =
    (427342645851489/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 552).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 552).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 552).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 552

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 552).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 552).criticalRate j.val*(generalMeanRows 552).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 552).c*(generalMeanRows 552).criticalPoint j.val)).2-
      (generalMeanRows 552).J/2-(generalMeanRows 552).error (generalMeanGrid j.val)+
      (generalMeanRows 552).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 552).c)).2-
      (generalMeanRows 552).J/2-(generalMeanRows 552).error 4 := by
  have he : (generalMeanRows 552).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 552) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 552)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0552

/-! Kernel-checked entropy margins for general spectral rectangle 553. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0553
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5241867463, 5074071544, 4913703475, 4760334881, 4613567906, 4473032549, 4338384281, 4209301920, 4085485712, 3966655613, 3852549731, 3742922922, 3637545514, 3536202147, 3438690718, 3344821421, 3254415862, 3167306258, 3083334696, 3002352458, 2924219392, 2848803342, 2775979614, 2705630494, 2637644788, 2571917408, 2508348984, 2446845504, 2387317979, 2329682136, 2273858130, 2219770270, 2167346778, 2116519548, 2067223934, 2019398544, 1972985055, 1927928030, 1884174758, 1841675094, 1800381319, 1760248001, 1721231866, 1683291684, 1646388152, 1610483790, 1575542843, 1541531187, 1508416243, 1476166893, 1444753407, 1414147364, 1384321587, 1355250080, 1326907964, 1299271423, 1272317647, 1246024782, 1220371884, 1195338871, 1170906482, 1147056233, 1123770386, 1101031906, 1078824428, 1057132230, 1035940195, 1015233789, 994999026, 975222452, 955891112, 936992530, 918514687, 900446001, 882775307, 865491836, 848585200, 832045374, 815862680, 800027772, 784531622, 769365507, 754520992, 739989924, 725764414, 711836832, 698199790, 684846137, 671768947, 658961511, 646417327, 634130092, 622093696, 610302211, 598749889, 587431150, 576340577, 565472911, 554823046, 544386020, 534157012, 524131337, 514304439, 504671889, 495229378, 485972715, 476897822, 468000729, 459277571, 450724586, 442338108, 434114568, 426050487, 418142477, 410387232, 402781532, 395322238, 388006285, 380830686, 373792528, 366888965]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 553).prefactor = (4639809859591029/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 553).cutoff/(generalMeanRows 553).c)).2 =
    (419590669047169/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 553).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 553).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 553).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 553

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 553).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 553).criticalRate j.val*(generalMeanRows 553).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 553).c*(generalMeanRows 553).criticalPoint j.val)).2-
      (generalMeanRows 553).J/2-(generalMeanRows 553).error (generalMeanGrid j.val)+
      (generalMeanRows 553).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 553).c)).2-
      (generalMeanRows 553).J/2-(generalMeanRows 553).error 4 := by
  have he : (generalMeanRows 553).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 553) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 553)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0553

/-! Kernel-checked entropy margins for general spectral rectangle 554. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0554
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5172524216, 5004429664, 4843787350, 4690168988, 4543176731, 4402440517, 4267615695, 4138380899, 4014436142, 3895501099, 3781313558, 3671628017, 3566214414, 3464856973, 3367353149, 3273512672, 3183156669, 3096116860, 3012234825, 2931361326, 2853355686, 2778085216, 2705424689, 2635255850, 2567466966, 2501952410, 2438612275, 2377352013, 2318082107, 2260717756, 2205178594, 2151388417, 2099274937, 2048769549, 1999807114, 1952325756, 1906266675, 1861573969, 1818194466, 1776077577, 1735175140, 1695441297, 1656832353, 1619306670, 1582824544, 1547348107, 1512841223, 1479269401, 1446599699, 1414800653, 1383842189, 1353695557, 1324333260, 1295728989, 1267857565, 1240694877, 1214217832, 1188404301, 1163233073, 1138683810, 1114736999, 1091373918, 1068576594, 1046327768, 1024610858, 1003409932, 982709672, 962495346, 942752785, 923468350, 904628913, 886221831, 868234924, 850656456, 833475110, 816679977, 800260530, 784206615, 768508425, 753156496, 738141683, 723455151, 709088363, 695033061, 681281262, 667825243, 654657529, 641770886, 629158307, 616813009, 604728417, 592898161, 581316066, 569976145, 558872590, 547999766, 537352208, 526924608, 516711813, 506708820, 496910768, 487312935, 477910730, 468699694, 459675487, 450833892, 442170804, 433682232, 425364289, 417213195, 409225268, 401396923, 393724669, 386205104, 378834915, 371610874, 364529832, 357588723, 350784554, 344114410, 337575446]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 554).prefactor = (4642351893164733/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 554).cutoff/(generalMeanRows 554).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 554).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 554).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 554).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 554

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 554).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 554).criticalRate j.val*(generalMeanRows 554).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 554).c*(generalMeanRows 554).criticalPoint j.val)).2-
      (generalMeanRows 554).J/2-(generalMeanRows 554).error (generalMeanGrid j.val)+
      (generalMeanRows 554).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 554).c)).2-
      (generalMeanRows 554).J/2-(generalMeanRows 554).error 4 := by
  have he : (generalMeanRows 554).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 554) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 554)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0554

/-! Kernel-checked entropy margins for general spectral rectangle 555. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0555
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5251585194, 5083477369, 4922804501, 4769138304, 4622080984, 4481262575, 4346338565, 4216987760, 4092910384, 3973826346, 3859473699, 3749607226, 3643997170, 3542428079, 3444697746, 3350616254, 3260005091, 3172696351, 3088531993, 3007363163, 2929049577, 2853458937, 2780466413, 2709954146, 2641810800, 2575931145, 2512215667, 2450570212, 2390905651, 2333137570, 2277185983, 2222975065, 2170432899, 2119491248, 2070085334, 2022153636, 1975637703, 1930481976, 1886633621, 1844042375, 1802660402, 1762442157, 1723344256, 1685325361, 1648346064, 1612368781, 1577357660, 1543278480, 1510098568, 1477786715, 1446313102, 1415649221, 1385767815, 1356642805, 1328249236, 1300563214, 1273561858, 1247223242, 1221526355, 1196451047, 1171977994, 1148088652, 1124765221, 1101990609, 1079748397, 1058022808, 1036798674, 1016061410, 995796985, 975991895, 956633142, 937708207, 919205031, 901111991, 883417883, 866111901, 849183622, 832622988, 816420286, 800566140, 785051491, 769867586, 755005963, 740458441, 726217106, 712274301, 698622617, 685254877, 672164135, 659343659, 646786927, 634487618, 622439601, 610636932, 599073843, 587744738, 576644185, 565766910, 555107791, 544661852, 534424259, 524390313, 514555447, 504915218, 495465307, 486201511, 477119742, 468216020, 459486469, 450927319, 442534894, 434305617, 426236002, 418322649, 410562249, 402951573, 395487473, 388166880, 380986800, 373944313, 367036568]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 555).prefactor = (4641081102085827/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 555).cutoff/(generalMeanRows 555).c)).2 =
    (209075391994591/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 555).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 555).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 555).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 555

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 555).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 555).criticalRate j.val*(generalMeanRows 555).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 555).c*(generalMeanRows 555).criticalPoint j.val)).2-
      (generalMeanRows 555).J/2-(generalMeanRows 555).error (generalMeanGrid j.val)+
      (generalMeanRows 555).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 555).c)).2-
      (generalMeanRows 555).J/2-(generalMeanRows 555).error 4 := by
  have he : (generalMeanRows 555).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 555) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 555)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0555

/-! Kernel-checked entropy margins for general spectral rectangle 556. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0556
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5260464341, 5092072287, 4931127760, 4777201751, 4629895793, 4488839295, 4353687161, 4224117656, 4099830495, 3980545116, 3865999126, 3755946895, 3650158279, 3548417459, 3450521888, 3356281327, 3265516963, 3178060605, 3093753945, 3012447880, 2934001884, 2858283439, 2785167502, 2714536016, 2646277456, 2580286415, 2516463210, 2454713527, 2394948088, 2337082335, 2281036148, 2226733573, 2174102571, 2123074790, 2073585342, 2025572604, 1978978024, 1933745949, 1889823457, 1847160200, 1805708260, 1765422016, 1726258010, 1688174835, 1651133014, 1615094903, 1580024587, 1545887787, 1512651776, 1480285291, 1448758464, 1418042738, 1388110810, 1358936557, 1330494981, 1302762149, 1275715140, 1249331992, 1223591657, 1198473954, 1173959522, 1150029789, 1126666924, 1103853806, 1081573988, 1059811666, 1038551647, 1017779321, 997480634, 977642059, 958250575, 939293643, 920759182, 902635551, 884911526, 867576285, 850619384, 834030750, 817800653, 801919702, 786378821, 771169244, 756282494, 741710375, 727444961, 713478583, 699803817, 686413476, 673300600, 660458448, 647880486, 635560381, 623491994, 611669369, 600086730, 588738471, 577619150, 566723484, 556046343, 545582743, 535327840, 525276929, 515425434, 505768906, 496303018, 487023559, 477926435, 469007658, 460263348, 451689726, 443283113, 435039922, 426956663, 419029931, 411256410, 403632866, 396156146, 388823175, 381630956, 374576561, 367657138]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 556).prefactor = (4648928035861097/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 556).cutoff/(generalMeanRows 556).c)).2 =
    (209075391994591/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 556).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 556).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 556).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 556

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 556).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 556).criticalRate j.val*(generalMeanRows 556).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 556).c*(generalMeanRows 556).criticalPoint j.val)).2-
      (generalMeanRows 556).J/2-(generalMeanRows 556).error (generalMeanGrid j.val)+
      (generalMeanRows 556).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 556).c)).2-
      (generalMeanRows 556).J/2-(generalMeanRows 556).error 4 := by
  have he : (generalMeanRows 556).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 556) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 556)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0556

/-! Kernel-checked entropy margins for general spectral rectangle 557. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0557
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5181305260, 5012925346, 4852010320, 4698131170, 4550889375, 4409914243, 4274860538, 4145406348, 4021251178, 3902114227, 3787732838, 3677861091, 3572268535, 3470739026, 3373069677, 3279069893, 3188560498, 3101372928, 3017348492, 2936337699, 2858199635, 2782801384, 2710017506, 2639729546, 2571825581, 2506199805, 2442752142, 2381387883, 2322017358, 2264555624, 2208922177, 2155040684, 2102838734, 2052247607, 2003202051, 1955640088, 1909502815, 1864734237, 1821281092, 1779092703, 1738120830, 1698319533, 1659645046, 1622055657, 1585511598, 1549974935, 1515409472, 1481780656, 1449055494, 1417202464, 1386191444, 1355993634, 1326581491, 1297928661, 1270009921, 1242801121, 1216279127, 1190421775, 1165207816, 1140616876, 1116629412, 1093226670, 1070390644, 1048104048, 1026350271, 1005113353, 984377951, 964129309, 944353232, 925036060, 906164640, 887726310, 869708868, 852100557, 834890044, 818066399, 801619079, 785537909, 769813070, 754435079, 739394776, 724683312, 710292134, 696212971, 682437827, 668958965, 655768897, 642860377, 630226387, 617860130, 605755023, 593904684, 582302927, 570943755, 559821350, 548930069, 538264435, 527819132, 517588999, 507569025, 497754340, 488140213, 478722047, 469495374, 460455847, 451599242, 442921447, 434418465, 426086401, 417921470, 409919982, 402078348, 394393069, 386860738, 379478038, 372241732, 365148670, 358195777, 351380058, 344698590, 338148525]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 557).prefactor = (4650232899772679/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 557).cutoff/(generalMeanRows 557).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 557).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 557).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 557).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 557

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 557).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 557).criticalRate j.val*(generalMeanRows 557).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 557).c*(generalMeanRows 557).criticalPoint j.val)).2-
      (generalMeanRows 557).J/2-(generalMeanRows 557).error (generalMeanGrid j.val)+
      (generalMeanRows 557).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 557).c)).2-
      (generalMeanRows 557).J/2-(generalMeanRows 557).error 4 := by
  have he : (generalMeanRows 557).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 557) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 557)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0557

/-! Kernel-checked entropy margins for general spectral rectangle 558. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0558
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5190101212, 5021435450, 4860247250, 4706106870, 4558615111, 4417400655, 4282117679, 4152443724, 4028077784, 3908738583, 3794163015, 3684104747, 3578332934, 3476631065, 3378795909, 3284636548, 3193973502, 3106637918, 3022470840, 2941322521, 2863051807, 2787525557, 2714618119, 2644210836, 2576191595, 2510454411, 2446899037, 2385430604, 2325959290, 2268400007, 2212672114, 2158699151, 2106408581, 2055731569, 2006602752, 1958960046, 1912744449, 1867899870, 1824372958, 1782112949, 1741071520, 1701202655, 1662462513, 1624809312, 1588203214, 1552606223, 1517982080, 1484296175, 1451515457, 1419608353, 1388544687, 1358295613, 1328833538, 1300132066, 1272165931, 1244910940, 1218343922, 1192442673, 1167185910, 1142553224, 1118525038, 1095082567, 1072207774, 1049883343, 1028092636, 1006819666, 986049063, 965766047, 945956397, 926606431, 907702975, 889233343, 871185314, 853547111, 836307381, 819455175, 802979933, 786871464, 771119930, 755715832, 740649997, 725913558, 711497949, 697394885, 683596356, 670094611, 656882152, 643951717, 631296279, 618909030, 606783372, 594912916, 583291463, 571913007, 560771721, 549861950, 539178210, 528715175, 518467675, 508430690, 498599343, 488968895, 479534741, 470292404, 461237532, 452365891, 443673365, 435155947, 426809739, 418630947, 410615876, 402760929, 395062603, 387517486, 380122252, 372873662, 365768558, 358803862, 351976572, 345283762, 338722577]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 558).prefactor = (1164531821358037/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 558).cutoff/(generalMeanRows 558).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 558).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 558).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 558).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 558

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 558).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 558).criticalRate j.val*(generalMeanRows 558).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 558).c*(generalMeanRows 558).criticalPoint j.val)).2-
      (generalMeanRows 558).J/2-(generalMeanRows 558).error (generalMeanGrid j.val)+
      (generalMeanRows 558).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 558).c)).2-
      (generalMeanRows 558).J/2-(generalMeanRows 558).error 4 := by
  have he : (generalMeanRows 558).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 558) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 558)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0558

/-! Kernel-checked entropy margins for general spectral rectangle 559. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0559
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5157867064, 4990276850, 4830089499, 4676881514, 4530259419, 4389857134, 4255333638, 4126370874, 4002671870, 3883959045, 3769972686, 3660469564, 3555221685, 3454015149, 3356649117, 3262934865, 3172694920, 3085762273, 3001979650, 2921198849, 2843280125, 2768091630, 2695508893, 2625414334, 2557696827, 2492251286, 2428978285, 2367783703, 2308578401, 2251277910, 2195802156, 2142075189, 2090024943, 2039583001, 1990684387, 1943267362, 1897273239, 1852646211, 1809333182, 1767283619, 1726449406, 1686784713, 1648245868, 1610791236, 1574381114, 1538977624, 1504544615, 1471047570, 1438453522, 1406730970, 1375849805, 1345781236, 1316497722, 1287972910, 1260181570, 1233099545, 1206703690, 1180971827, 1155882692, 1131415895, 1107551874, 1084271855, 1061557814, 1039392443, 1017759111, 996641836, 976025255, 955894590, 936235626, 917034683, 898278589, 879954661, 862050679, 844554870, 827455881, 810742768, 794404971, 778432302, 762814927, 747543350, 732608400, 718001216, 703713234, 689736177, 676062037, 662683070, 649591784, 636780924, 624243469, 611972618, 599961783, 588204580, 576694822, 565426510, 554393827, 543591128, 533012939, 522653945, 512508987, 502573056, 492841287, 483308952, 473971458, 464824343, 455863265, 447084005, 438482459, 430054634, 421796645, 413704711, 405775153, 398004388, 390388926, 382925370, 375610409, 368440817, 361413452, 354525250, 347773224, 341154463, 334666128]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 559).prefactor = (4599603533063833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 559).cutoff/(generalMeanRows 559).c)).2 =
    (80657989777483/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 559).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 559).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 559).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 559

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 559).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 559).criticalRate j.val*(generalMeanRows 559).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 559).c*(generalMeanRows 559).criticalPoint j.val)).2-
      (generalMeanRows 559).J/2-(generalMeanRows 559).error (generalMeanGrid j.val)+
      (generalMeanRows 559).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 559).c)).2-
      (generalMeanRows 559).J/2-(generalMeanRows 559).error 4 := by
  have he : (generalMeanRows 559).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 559) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 559)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0559

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock07 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 7 i) := by
  fin_cases i
  · exact EntropyRow0490.numerical
  · exact EntropyRow0491.numerical
  · exact EntropyRow0492.numerical
  · exact EntropyRow0493.numerical
  · exact EntropyRow0494.numerical
  · exact EntropyRow0495.numerical
  · exact EntropyRow0496.numerical
  · exact EntropyRow0497.numerical
  · exact EntropyRow0498.numerical
  · exact EntropyRow0499.numerical
  · exact EntropyRow0500.numerical
  · exact EntropyRow0501.numerical
  · exact EntropyRow0502.numerical
  · exact EntropyRow0503.numerical
  · exact EntropyRow0504.numerical
  · exact EntropyRow0505.numerical
  · exact EntropyRow0506.numerical
  · exact EntropyRow0507.numerical
  · exact EntropyRow0508.numerical
  · exact EntropyRow0509.numerical
  · exact EntropyRow0510.numerical
  · exact EntropyRow0511.numerical
  · exact EntropyRow0512.numerical
  · exact EntropyRow0513.numerical
  · exact EntropyRow0514.numerical
  · exact EntropyRow0515.numerical
  · exact EntropyRow0516.numerical
  · exact EntropyRow0517.numerical
  · exact EntropyRow0518.numerical
  · exact EntropyRow0519.numerical
  · exact EntropyRow0520.numerical
  · exact EntropyRow0521.numerical
  · exact EntropyRow0522.numerical
  · exact EntropyRow0523.numerical
  · exact EntropyRow0524.numerical
  · exact EntropyRow0525.numerical
  · exact EntropyRow0526.numerical
  · exact EntropyRow0527.numerical
  · exact EntropyRow0528.numerical
  · exact EntropyRow0529.numerical
  · exact EntropyRow0530.numerical
  · exact EntropyRow0531.numerical
  · exact EntropyRow0532.numerical
  · exact EntropyRow0533.numerical
  · exact EntropyRow0534.numerical
  · exact EntropyRow0535.numerical
  · exact EntropyRow0536.numerical
  · exact EntropyRow0537.numerical
  · exact EntropyRow0538.numerical
  · exact EntropyRow0539.numerical
  · exact EntropyRow0540.numerical
  · exact EntropyRow0541.numerical
  · exact EntropyRow0542.numerical
  · exact EntropyRow0543.numerical
  · exact EntropyRow0544.numerical
  · exact EntropyRow0545.numerical
  · exact EntropyRow0546.numerical
  · exact EntropyRow0547.numerical
  · exact EntropyRow0548.numerical
  · exact EntropyRow0549.numerical
  · exact EntropyRow0550.numerical
  · exact EntropyRow0551.numerical
  · exact EntropyRow0552.numerical
  · exact EntropyRow0553.numerical
  · exact EntropyRow0554.numerical
  · exact EntropyRow0555.numerical
  · exact EntropyRow0556.numerical
  · exact EntropyRow0557.numerical
  · exact EntropyRow0558.numerical
  · exact EntropyRow0559.numerical
end SingularValueBounds.KL.Certificates
