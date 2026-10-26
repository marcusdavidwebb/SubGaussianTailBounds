import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 1050. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1050
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5575577201, 5389750921, 5211757191, 5041170426, 4877594583, 4720660568, 4570023930, 4425362803, 4286376051, 4152781609, 4024314985, 3900727907, 3781787095, 3667273148, 3556979537, 3450711676, 3348286084, 3249529612, 3154278742, 3062378931, 2973684023, 2888055696, 2805362960, 2725481685, 2648294176, 2573688770, 2501559467, 2431805587, 2364331450, 2299046083, 2235862940, 2174699651, 2115477776, 2058122589, 2002562861, 1948730674, 1896561234, 1845992699, 1796966023, 1749424804, 1703315145, 1658585520, 1615186653, 1573071398, 1532194633, 1492513157, 1453985589, 1416572282, 1380235233, 1344938006, 1310645650, 1277324632, 1244942766, 1213469150, 1182874104, 1153129114, 1124206775, 1096080744, 1068725685, 1042117230, 1016231929, 991047213, 966541352, 942693419, 919483255, 896891434, 874899233, 853488600, 832642127, 812343021, 792575078, 773322662, 754570675, 736304542, 718510183, 701173998, 684282842, 667824015, 651785235, 636154628, 620920709, 606072369, 591598858, 577489772, 563735039, 550324911, 537249944, 524500994, 512069201, 499945980, 488123012, 476592233, 465345824, 454376206, 443676026, 433238153, 423055669, 413121862, 403430216, 393974408, 384748301, 375745934, 366961521, 358389441, 350024235, 341860600, 333893382, 326117574, 318528309, 311120859, 303890623, 296833133, 289944041, 283219120, 276654259, 270245458, 263988829, 257880585, 251917045, 246094625, 240409837]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1050).prefactor = (5217144433682381/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1050).cutoff/(generalMeanRows 1050).c)).2 =
    (338124664959033/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1050).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1050).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1050).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1050

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1050).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1050).criticalRate j.val*(generalMeanRows 1050).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1050).c*(generalMeanRows 1050).criticalPoint j.val)).2-
      (generalMeanRows 1050).J/2-(generalMeanRows 1050).error (generalMeanGrid j.val)+
      (generalMeanRows 1050).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1050).c)).2-
      (generalMeanRows 1050).J/2-(generalMeanRows 1050).error 4 := by
  have he : (generalMeanRows 1050).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1050) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1050)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1050

/-! Kernel-checked entropy margins for general spectral rectangle 1051. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1051
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5690381473, 5498534528, 5314811044, 5138769650, 4969999575, 4808117968, 4652767511, 4503614284, 4360345846, 4222669523, 4090310850, 3963012170, 3840531369, 3722640721, 3609125838, 3499784720, 3394426878, 3292872539, 3194951913, 3100504522, 3009378587, 2921430454, 2836524075, 2754530520, 2675327537, 2598799131, 2524835186, 2453331106, 2384187487, 2317309810, 2252608153, 2189996930, 2129394635, 2070723619, 2013909868, 1958882805, 1905575096, 1853922480, 1803863596, 1755339833, 1708295183, 1662676102, 1618431384, 1575512040, 1533871183, 1493463924, 1454247267, 1416180019, 1379222698, 1343337448, 1308487964, 1274639411, 1241758358, 1209812710, 1178771642, 1148605544, 1119285961, 1090785540, 1063077980, 1036137986, 1009941218, 984464254, 959684546, 935580382, 912130849, 889315797, 867115810, 845512168, 824486825, 804022372, 784102017, 764709557, 745829350, 727446299, 709545822, 692113838, 675136740, 658601382, 642495056, 626805479, 611520772, 596629447, 582120390, 567982850, 554206420, 540781027, 527696921, 514944660, 502515097, 490399375, 478588911, 467075389, 455850746, 444907171, 434237086, 423833147, 413688228, 403795418, 394148013, 384739507, 375563586, 366614124, 357885172, 349370954, 341065863, 332964452, 325061433, 317351666, 309830161, 302492066, 295332668, 288347386, 281531768, 274881484, 268392326, 262060203, 255881135, 249851253, 243966792, 238224091, 232619587]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1051).prefactor = (5402261213923671/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1051).cutoff/(generalMeanRows 1051).c)).2 =
    (4153671808103/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1051).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1051).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1051).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1051

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1051).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1051).criticalRate j.val*(generalMeanRows 1051).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1051).c*(generalMeanRows 1051).criticalPoint j.val)).2-
      (generalMeanRows 1051).J/2-(generalMeanRows 1051).error (generalMeanGrid j.val)+
      (generalMeanRows 1051).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1051).c)).2-
      (generalMeanRows 1051).J/2-(generalMeanRows 1051).error 4 := by
  have he : (generalMeanRows 1051).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1051) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1051)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1051

/-! Kernel-checked entropy margins for general spectral rectangle 1052. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1052
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5892289836, 5693635703, 5503393269, 5321105505, 5146347063, 4978721510, 4817858847, 4663413305, 4515061361, 4372499952, 4235444875, 4103629333, 3976802621, 3854728930, 3737186267, 3623965465, 3514869274, 3409711544, 3308316459, 3210517849, 3116158547, 3025089804, 2937170743, 2852267861, 2770254566, 2691010749, 2614422386, 2540381169, 2468784169, 2399533512, 2332536086, 2267703266, 2204950657, 2144197853, 2085368214, 2028388658, 1973189465, 1919704090, 1867868997, 1817623495, 1768909588, 1721671832, 1675857206, 1631414981, 1588296607, 1546455601, 1505847444, 1466429478, 1428160823, 1391002278, 1354916251, 1319866670, 1285818919, 1252739762, 1220597283, 1189360820, 1159000908, 1129489223, 1100798533, 1072902643, 1045776351, 1019395404, 993736453, 968777015, 944495436, 920870852, 897883155, 875512965, 853741592, 832551011, 811923835, 791843283, 772293162, 753257836, 734722208, 716671694, 699092208, 681970136, 665292320, 649046039, 633218994, 617799289, 602775416, 588136242, 573870991, 559969233, 546420872, 533216129, 520345536, 507799920, 495570392, 483648342, 472025423, 460693543, 449644858, 438871762, 428366877, 418123046, 408133328, 398390986, 388889482, 379622472, 370583795, 361767472, 353167696, 344778828, 336595391, 328612063, 320823677, 313225209, 305811778, 298578642, 291521189, 284634937, 277915529, 271358727, 264960411, 258716574, 252623318, 246676852, 240873488]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1052).prefactor = (5593946380906501/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1052).cutoff/(generalMeanRows 1052).c)).2 =
    (4153671808103/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1052).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1052).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1052).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1052

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1052).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1052).criticalRate j.val*(generalMeanRows 1052).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1052).c*(generalMeanRows 1052).criticalPoint j.val)).2-
      (generalMeanRows 1052).J/2-(generalMeanRows 1052).error (generalMeanGrid j.val)+
      (generalMeanRows 1052).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1052).c)).2-
      (generalMeanRows 1052).J/2-(generalMeanRows 1052).error 4 := by
  have he : (generalMeanRows 1052).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1052) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1052)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1052

/-! Kernel-checked entropy margins for general spectral rectangle 1053. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1053
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6435508793, 6242523864, 6057428008, 5879785945, 5709193173, 5545273245, 5387675360, 5236072196, 5090157972, 4949646706, 4814270641, 4683778828, 4557935836, 4436520590, 4319325303, 4206154515, 4096824204, 3991160984, 3889001359, 3790191051, 3694584371, 3602043650, 3512438705, 3425646356, 3341549973, 3260039061, 3181008873, 3104360054, 3029998308, 2957834091, 2887782324, 2819762129, 2753696577, 2689512463, 2627140083, 2566513041, 2507568054, 2450244780, 2394485656, 2340235739, 2287442565, 2236056015, 2186028188, 2137313280, 2089867475, 2043648843, 1998617234, 1954734193, 1911962870, 1870267939, 1829615519, 1789973105, 1751309497, 1713594735, 1676800041, 1640897761, 1605861308, 1571665113, 1538284579, 1505696031, 1473876675, 1442804558, 1412458527, 1382818197, 1353863909, 1325576705, 1297938292, 1270931014, 1244537826, 1218742265, 1193528423, 1168880930, 1144784924, 1121226036, 1098190362, 1075664452, 1053635285, 1032090256, 1011017155, 990404155, 970239794, 950512964, 931212894, 912329137, 893851561, 875770332, 858075909, 840759027, 823810690, 807222162, 790984953, 775090817, 759531736, 744299919, 729387787, 714787971, 700493303, 686496809, 672791701, 659371373, 646229395, 633359505, 620755605, 608411755, 596322169, 584481210, 572883384, 561523335, 550395843, 539495819, 528818301, 518358448, 508111539, 498072969, 488238245, 478602982, 469162902, 459913828, 450851684, 441972490, 433272359]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1053).prefactor = (2705913355760017/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1053).cutoff/(generalMeanRows 1053).c)).2 =
    (8143693416309/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1053).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1053).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1053).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1053

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1053).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1053).criticalRate j.val*(generalMeanRows 1053).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1053).c*(generalMeanRows 1053).criticalPoint j.val)).2-
      (generalMeanRows 1053).J/2-(generalMeanRows 1053).error (generalMeanGrid j.val)+
      (generalMeanRows 1053).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1053).c)).2-
      (generalMeanRows 1053).J/2-(generalMeanRows 1053).error 4 := by
  have he : (generalMeanRows 1053).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1053) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1053)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1053

/-! Kernel-checked entropy margins for general spectral rectangle 1054. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1054
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6749956169, 6550236873, 6358650184, 6174746884, 5998109555, 5828349776, 5665105623, 5508039434, 5356835801, 5211199772, 5070855224, 4935543395, 4805021554, 4679061795, 4557449940, 4439984537, 4326475948, 4216745516, 4110624796, 4007954860, 3908585644, 3812375364, 3719189962, 3628902607, 3541393227, 3456548079, 3374259351, 3294424793, 3216947372, 3141734957, 3068700022, 2997759370, 2928833879, 2861848261, 2796730840, 2733413347, 2671830722, 2611920936, 2553624818, 2496885900, 2441650267, 2387866415, 2335485127, 2284459342, 2234744048, 2186296170, 2139074467, 2093039442, 2048153247, 2004379601, 1961683713, 1920032201, 1879393027, 1839735429, 1801029858, 1763247917, 1726362310, 1690346785, 1655176085, 1620825904, 1587272837, 1554494344, 1522468707, 1491174992, 1460593014, 1430703305, 1401487081, 1372926208, 1345003179, 1317701086, 1291003589, 1264894897, 1239359744, 1214383363, 1189951469, 1166050240, 1142666292, 1119786668, 1097398816, 1075490576, 1054050161, 1033066146, 1012527451, 992423329, 972743353, 953477405, 934615660, 916148583, 898066908, 880361637, 863024026, 846045577, 829418028, 813133346, 797183719, 781561545, 766259432, 751270182, 736586792, 722202441, 708110489, 694304469, 680778082, 667525189, 654539809, 641816113, 629348419, 617131186, 605159013, 593426631, 581928901, 570660810, 559617467, 548794099, 538186047, 527788764, 517597812, 507608856, 497817665, 488220105, 478812141]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1054).prefactor = (1118381869808811/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1054).cutoff/(generalMeanRows 1054).c)).2 =
    (206622647713571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1054).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1054).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1054).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1054

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1054).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1054).criticalRate j.val*(generalMeanRows 1054).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1054).c*(generalMeanRows 1054).criticalPoint j.val)).2-
      (generalMeanRows 1054).J/2-(generalMeanRows 1054).error (generalMeanGrid j.val)+
      (generalMeanRows 1054).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1054).c)).2-
      (generalMeanRows 1054).J/2-(generalMeanRows 1054).error 4 := by
  have he : (generalMeanRows 1054).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1054) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1054)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1054

/-! Kernel-checked entropy margins for general spectral rectangle 1055. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1055
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6934295688, 6711270764, 6497521289, 6292542887, 6095866319, 5907054395, 5725699226, 5551419765, 5383859607, 5222685006, 5067583093, 4918260259, 4774440703, 4635865098, 4502289392, 4373483707, 4249231339, 4129327836, 4013580164, 3901805931, 3793832679, 3689497235, 3588645107, 3491129927, 3396812943, 3305562541, 3217253806, 3131768113, 3048992751, 2968820570, 2891149651, 2815883007, 2742928291, 2672197540, 2603606919, 2537076496, 2472530024, 2409894736, 2349101159, 2290082936, 2232776659, 2177121711, 2123060123, 2070536432, 2019497558, 1969892673, 1921673095, 1874792175, 1829205197, 1784869283, 1741743301, 1699787781, 1658964834, 1619238075, 1580572553, 1542934684, 1506292185, 1470614011, 1435870305, 1402032335, 1369072450, 1336964025, 1305681420, 1275199934, 1245495762, 1216545958, 1188328396, 1160821736, 1134005390, 1107859488, 1082364849, 1057502955, 1033255916, 1009606452, 986537863, 964034008, 942079279, 920658584, 899757322, 879361368, 859457051, 840031137, 821070812, 802563668, 784497683, 766861212, 749642969, 732832013, 716417738, 700389860, 684738403, 669453691, 654526335, 639947224, 625707513, 611798616, 598212197, 584940159, 571974639, 559307995, 546932805, 534841854, 523028131, 511484818, 500205289, 489183098, 478411979, 467885833, 457598731, 447544901, 437718728, 428114746, 418727636, 409552219, 400583454, 391816431, 383246369, 374868612, 366678625, 358671988, 350844397]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1055).prefactor = (1242156892934647/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1055).cutoff/(generalMeanRows 1055).c)).2 =
    (177912121029217/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1055).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1055).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1055).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1055

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1055).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1055).criticalRate j.val*(generalMeanRows 1055).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1055).c*(generalMeanRows 1055).criticalPoint j.val)).2-
      (generalMeanRows 1055).J/2-(generalMeanRows 1055).error (generalMeanGrid j.val)+
      (generalMeanRows 1055).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1055).c)).2-
      (generalMeanRows 1055).J/2-(generalMeanRows 1055).error 4 := by
  have he : (generalMeanRows 1055).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1055) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1055)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1055

/-! Kernel-checked entropy margins for general spectral rectangle 1056. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1056
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7192150619, 6987429074, 6790612444, 6601289064, 6419075561, 6243614330, 6074571297, 5911633924, 5754509427, 5602923178, 5456617272, 5315349231, 5178890835, 5047027066, 4919555147, 4796283668, 4677031790, 4561628517, 4449912031, 4341729083, 4236934432, 4135390329, 4036966042, 3941537423, 3848986496, 3759201086, 3672074473, 3587505071, 3505396125, 3425655436, 3348195102, 3272931275, 3199783942, 3128676704, 3059536591, 2992293872, 2926881883, 2863236868, 2801297827, 2741006372, 2682306597, 2625144951, 2569470118, 2515232910, 2462386157, 2410884616, 2360684870, 2311745244, 2264025722, 2217487870, 2172094757, 2127810892, 2084602149, 2042435715, 2001280019, 1961104684, 1921880472, 1883579231, 1846173846, 1809638199, 1773947120, 1739076348, 1705002493, 1671702997, 1639156098, 1607340800, 1576236837, 1545824644, 1516085329, 1487000642, 1458552954, 1430725228, 1403500994, 1376864330, 1350799839, 1325292624, 1300328276, 1275892848, 1251972840, 1228555181, 1205627213, 1183176676, 1161191690, 1139660744, 1118572680, 1097916680, 1077682255, 1057859229, 1038437735, 1019408193, 1000761310, 982488064, 964579694, 947027693, 929823799, 912959985, 896428450, 880221616, 864332112, 848752776, 833476641, 818496933, 803807059, 789400608, 775271339, 761413179, 747820216, 734486693, 721407005, 708575692, 695987436, 683637056, 671519502, 659629854, 647963316, 636515212, 625280981, 614256179, 603436468, 592817619, 582395505]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1056).prefactor = (5174136577301751/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1056).cutoff/(generalMeanRows 1056).c)).2 =
    (327972293495017/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1056).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1056).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1056).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1056

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1056).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1056).criticalRate j.val*(generalMeanRows 1056).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1056).c*(generalMeanRows 1056).criticalPoint j.val)).2-
      (generalMeanRows 1056).J/2-(generalMeanRows 1056).error (generalMeanGrid j.val)+
      (generalMeanRows 1056).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1056).c)).2-
      (generalMeanRows 1056).J/2-(generalMeanRows 1056).error 4 := by
  have he : (generalMeanRows 1056).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1056) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1056)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1056

/-! Kernel-checked entropy margins for general spectral rectangle 1057. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1057
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6893823966, 6697080747, 6507997417, 6326171435, 6151228012, 5982817638, 5820613903, 5664311534, 5513624656, 5368285223, 5228041612, 5092657352, 4961909977, 4835589988, 4713499909, 4595453423, 4481274597, 4370797161, 4263863852, 4160325820, 4060042067, 3962878948, 3868709697, 3777414001, 3688877596, 3602991901, 3519653674, 3438764699, 3360231485, 3283964997, 3209880399, 3137896817, 3067937116, 2999927695, 2933798292, 2869481803, 2806914112, 2746033936, 2686782671, 2629104256, 2572945038, 2518253654, 2464980911, 2413079677, 2362504780, 2313212911, 2265162532, 2218313789, 2172628431, 2128069735, 2084602434, 2042192644, 2000807802, 1960416607, 1920988957, 1882495899, 1844909571, 1808203159, 1772350845, 1737327765, 1703109969, 1669674374, 1636998734, 1605061598, 1573842279, 1543320820, 1513477964, 1484295121, 1455754347, 1427838308, 1400530263, 1373814034, 1347673985, 1322095003, 1297062469, 1272562246, 1248580657, 1225104465, 1202120858, 1179617432, 1157582174, 1136003448, 1114869979, 1094170842, 1073895446, 1054033523, 1034575115, 1015510563, 996830496, 978525820, 960587707, 943007589, 925777144, 908888289, 892333174, 876104169, 860193860, 844595040, 829300703, 814304035, 799598408, 785177377, 771034668, 757164177, 743559962, 730216239, 717127376, 704287887, 691692430, 679335800, 667212925, 655318863, 643648797, 632198029, 620961982, 609936190, 599116298, 588498058, 578077325, 567850056, 557812304]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1057).prefactor = (5051498850118719/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1057).cutoff/(generalMeanRows 1057).c)).2 =
    (343026113237427/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1057).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1057).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1057).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1057

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1057).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1057).criticalRate j.val*(generalMeanRows 1057).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1057).c*(generalMeanRows 1057).criticalPoint j.val)).2-
      (generalMeanRows 1057).J/2-(generalMeanRows 1057).error (generalMeanGrid j.val)+
      (generalMeanRows 1057).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1057).c)).2-
      (generalMeanRows 1057).J/2-(generalMeanRows 1057).error 4 := by
  have he : (generalMeanRows 1057).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1057) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1057)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1057

/-! Kernel-checked entropy margins for general spectral rectangle 1058. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1058
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6631868327, 6427193768, 6230664563, 6041855026, 5860368603, 5685835297, 5517909370, 5356267302, 5200605962, 5050640967, 4906105207, 4766747517, 4632331474, 4502634309, 4377445913, 4256567943, 4139812998, 4027003868, 3917972849, 3812561111, 3710618121, 3612001111, 3516574586, 3424209871, 3334784693, 3248182795, 3164293573, 3083011747, 3004237049, 2927873935, 2853831320, 2782022325, 2712364042, 2644777324, 2579186571, 2515519550, 2453707207, 2393683508, 2335385276, 2278752048, 2223725932, 2170251484, 2118275579, 2067747297, 2018617818, 1970840317, 1924369868, 1879163351, 1835179370, 1792378169, 1750721555, 1710172827, 1670696706, 1632259271, 1594827895, 1558371190, 1522858948, 1488262093, 1454552625, 1421703579, 1389688976, 1358483781, 1328063864, 1298405960, 1269487633, 1241287240, 1213783899, 1186957458, 1160788463, 1135258130, 1110348319, 1086041506, 1062320758, 1039169714, 1016572554, 994513987, 972979221, 951953952, 931424338, 911376986, 891798933, 872677629, 854000923, 835757045, 817934598, 800522535, 783510154, 766887081, 750643260, 734768941, 719254667, 704091268, 689269845, 674781766, 660618652, 646772371, 633235028, 619998957, 607056714, 594401069, 582024997, 569921675, 558084469, 546506936, 535182809, 524105998, 513270580, 502670794, 492301040, 482155867, 472229973, 462518199, 453015526, 443717066, 434618062, 425713883, 417000021, 408472083, 400125794, 391956987, 383961605]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1058).prefactor = (5304191381252729/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1058).cutoff/(generalMeanRows 1058).c)).2 =
    (76015036176011/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1058).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1058).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1058).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1058

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1058).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1058).criticalRate j.val*(generalMeanRows 1058).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1058).c*(generalMeanRows 1058).criticalPoint j.val)).2-
      (generalMeanRows 1058).J/2-(generalMeanRows 1058).error (generalMeanGrid j.val)+
      (generalMeanRows 1058).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1058).c)).2-
      (generalMeanRows 1058).J/2-(generalMeanRows 1058).error 4 := by
  have he : (generalMeanRows 1058).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1058) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1058)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1058

/-! Kernel-checked entropy margins for general spectral rectangle 1059. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1059
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6627006406, 6429957095, 6240719412, 6058880249, 5884054987, 5715884981, 5554035312, 5398192791, 5248064172, 5103374541, 4963865875, 4829295738, 4699436104, 4574072284, 4453001961, 4336034302, 4222989154, 4113696308, 4007994823, 3905732407, 3806764850, 3710955500, 3618174781, 3528299748, 3441213677, 3356805680, 3274970360, 3195607475, 3118621643, 3043922049, 2971422194, 2901039639, 2832695783, 2766315648, 2701827677, 2639163551, 2578258013, 2519048704, 2461476009, 2405482915, 2351014875, 2298019680, 2246447341, 2196249977, 2147381707, 2099798553, 2053458346, 2008320635, 1964346606, 1921499002, 1879742050, 1839041389, 1799364002, 1760678158, 1722953349, 1686160234, 1650270585, 1615257238, 1581094044, 1547755826, 1515218331, 1483458193, 1452452893, 1422180723, 1392620749, 1363752778, 1335557330, 1308015602, 1281109445, 1254821331, 1229134334, 1204032099, 1179498821, 1155519225, 1132078538, 1109162477, 1086757224, 1064849408, 1043426090, 1022474742, 1001983237, 981939827, 962333133, 943152127, 924386125, 906024765, 888058005, 870476103, 853269610, 836429358, 819946451, 803812252, 788018378, 772556689, 757419277, 742598463, 728086783, 713876986, 699962024, 686335043, 672989381, 659918558, 647116271, 634576389, 622292945, 610260133, 598472302, 586923949, 575609717, 564524390, 553662886, 543020256, 532591677, 522372450, 512357996, 502543850, 492925661, 483499186, 474260288, 465204933, 456329184]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1059).prefactor = (2581045037769017/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1059).cutoff/(generalMeanRows 1059).c)).2 =
    (170019881447567/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1059).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1059).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1059).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1059

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1059).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1059).criticalRate j.val*(generalMeanRows 1059).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1059).c*(generalMeanRows 1059).criticalPoint j.val)).2-
      (generalMeanRows 1059).J/2-(generalMeanRows 1059).error (generalMeanGrid j.val)+
      (generalMeanRows 1059).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1059).c)).2-
      (generalMeanRows 1059).J/2-(generalMeanRows 1059).error 4 := by
  have he : (generalMeanRows 1059).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1059) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1059)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1059

/-! Kernel-checked entropy margins for general spectral rectangle 1060. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1060
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6449033264, 6260059043, 6078599573, 5904252945, 5736645147, 5575427602, 5420274974, 5270883211, 5126967791, 4988262148, 4854516259, 4725495359, 4600978791, 4480758952, 4364640342, 4252438694, 4143980183, 4039100703, 3937645202, 3839467072, 3744427596, 3652395424, 3563246110, 3476861665, 3393130156, 3311945334, 3233206285, 3156817106, 3082686611, 3010728052, 2940858857, 2873000395, 2807077746, 2743019495, 2680757537, 2620226890, 2561365530, 2504114223, 2448416383, 2394217925, 2341467136, 2290114550, 2240112832, 2191416668, 2143982661, 2097769238, 2052736551, 2008846400, 1966062145, 1924348632, 1883672120, 1844000216, 1805301804, 1767546990, 1730707043, 1694754339, 1659662310, 1625405396, 1591958998, 1559299435, 1527403903, 1496250431, 1465817853, 1436085763, 1407034486, 1378645048, 1350899139, 1323779094, 1297267855, 1271348953, 1246006481, 1221225068, 1196989859, 1173286496, 1150101090, 1127420211, 1105230865, 1083520474, 1062276865, 1041488250, 1021143211, 1001230689, 981739966, 962660654, 943982681, 925696282, 907791983, 890260594, 873093196, 856281134, 839816001, 823689638, 807894118, 792421739, 777265020, 762416686, 747869669, 733617095, 719652279, 705968718, 692560086, 679420229, 666543154, 653923031, 641554182, 629431077, 617548332, 605900702, 594483076, 583290474, 572318042, 561561050, 551014886, 540675051, 530537161, 520596937, 510850207, 501292899, 491921041, 482730755, 473718258]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1060).prefactor = (1005392621033017/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1060).cutoff/(generalMeanRows 1060).c)).2 =
    (72880458304811/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1060).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1060).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1060).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1060

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1060).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1060).criticalRate j.val*(generalMeanRows 1060).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1060).c*(generalMeanRows 1060).criticalPoint j.val)).2-
      (generalMeanRows 1060).J/2-(generalMeanRows 1060).error (generalMeanGrid j.val)+
      (generalMeanRows 1060).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1060).c)).2-
      (generalMeanRows 1060).J/2-(generalMeanRows 1060).error 4 := by
  have he : (generalMeanRows 1060).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1060) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1060)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1060

/-! Kernel-checked entropy margins for general spectral rectangle 1061. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1061
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6249176749, 6053870873, 5866483944, 5686594234, 5513809103, 5347762442, 5188112391, 5034539300, 4886743910, 4744445709, 4607381466, 4475303893, 4347980446, 4225192230, 4106733007, 3992408294, 3882034537, 3775438356, 3672455855, 3572931988, 3476719976, 3383680772, 3293682568, 3206600335, 3122315404, 3040715075, 2961692257, 2885145130, 2810976834, 2739095181, 2669412383, 2601844801, 2536312713, 2472740092, 2411054402, 2351186409, 2293070000, 2236642018, 2181842099, 2128612533, 2076898119, 2026646037, 1977805728, 1930328776, 1884168801, 1839281359, 1795623843, 1753155396, 1711836822, 1671630508, 1632500347, 1594411668, 1557331165, 1521226837, 1486067921, 1451824843, 1418469155, 1385973490, 1354311511, 1323457863, 1293388132, 1264078801, 1235507212, 1207651528, 1180490698, 1154004421, 1128173118, 1102977897, 1078400526, 1054423405, 1031029541, 1008202522, 985926490, 964186126, 942966619, 922253653, 902033383, 882292418, 863017803, 844197001, 825817879, 807868687, 790338051, 773214953, 756488720, 740149009, 724185796, 708589366, 693350298, 678459456, 663907978, 649687269, 635788986, 622205035, 608927556, 595948921, 583261722, 570858763, 558733054, 546877807, 535286421, 523952485, 512869766, 502032202, 491433901, 481069133, 470932324, 461018052, 451321042, 441836159, 432558409, 423482929, 414604984, 405919966, 397423387, 389110876, 380978176, 373021140, 365235729, 357618005, 350164133]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1061).prefactor = (5241519206417281/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1061).cutoff/(generalMeanRows 1061).c)).2 =
    (16662356187213/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1061).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1061).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1061).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1061

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1061).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1061).criticalRate j.val*(generalMeanRows 1061).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1061).c*(generalMeanRows 1061).criticalPoint j.val)).2-
      (generalMeanRows 1061).J/2-(generalMeanRows 1061).error (generalMeanGrid j.val)+
      (generalMeanRows 1061).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1061).c)).2-
      (generalMeanRows 1061).J/2-(generalMeanRows 1061).error 4 := by
  have he : (generalMeanRows 1061).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1061) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1061)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1061

/-! Kernel-checked entropy margins for general spectral rectangle 1062. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1062
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6209188302, 6021786500, 5841950630, 5669272735, 5503373268, 5343898588, 5190518730, 5042925415, 4900830263, 4763963193, 4632070978, 4504915942, 4382274776, 4263937475, 4149706357, 4039395183, 3932828342, 3829840116, 3730274000, 3633982080, 3540824464, 3450668754, 3363389559, 3278868054, 3196991563, 3117653174, 3040751389, 2966189796, 2893876758, 2823725136, 2755652021, 2689578489, 2625429374, 2563133054, 2502621247, 2443828831, 2386693666, 2331156432, 2277160474, 2224651661, 2173578254, 2123890772, 2075541882, 2028486284, 1982680606, 1938083306, 1894654579, 1852356272, 1811151800, 1771006067, 1731885395, 1693757456, 1656591204, 1620356816, 1585025631, 1550570099, 1516963725, 1484181022, 1452197467, 1420989450, 1390534239, 1360809937, 1331795447, 1303470433, 1275815289, 1248811105, 1222439641, 1196683292, 1171525065, 1146948551, 1122937903, 1099477807, 1076553466, 1054150574, 1032255299, 1010854262, 989934519, 969483542, 949489205, 929939769, 910823861, 892130466, 873848911, 855968849, 838480252, 821373395, 804638844, 788267449, 772250331, 756578871, 741244703, 726239703, 711555981, 697185874, 683121935, 669356928, 655883819, 642695770, 629786132, 617148439, 604776400, 592663897, 580804973, 569193834, 557824838, 546692493, 535791450, 525116501, 514662573, 504424722, 494398135, 484578116, 474960094, 465539608, 456312313, 447273971, 438420449, 429747715, 421251839, 412928983, 404775407]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1062).prefactor = (2545512689266917/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1062).cutoff/(generalMeanRows 1062).c)).2 =
    (36833844355553/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1062).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1062).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1062).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1062

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1062).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1062).criticalRate j.val*(generalMeanRows 1062).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1062).c*(generalMeanRows 1062).criticalPoint j.val)).2-
      (generalMeanRows 1062).J/2-(generalMeanRows 1062).error (generalMeanGrid j.val)+
      (generalMeanRows 1062).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1062).c)).2-
      (generalMeanRows 1062).J/2-(generalMeanRows 1062).error 4 := by
  have he : (generalMeanRows 1062).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1062) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1062)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1062

/-! Kernel-checked entropy margins for general spectral rectangle 1063. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1063
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5914499369, 5722230083, 5537921014, 5361144434, 5191502179, 5028623052, 4872160515, 4721790618, 4577210151, 4438134981, 4304298552, 4175450534, 4051355598, 3931792303, 3816552087, 3705438346, 3598265593, 3494858691, 3395052146, 3298689464, 3205622555, 3115711185, 3028822477, 2944830439, 2863615538, 2785064302, 2709068948, 2635527045, 2564341190, 2495418715, 2428671415, 2364015287, 2301370293, 2240660137, 2181812058, 2124756632, 2069427593, 2015761660, 1963698379, 1913179972, 1864151196, 1816559211, 1770353458, 1725485538, 1681909107, 1639579769, 1598454980, 1558493957, 1519657590, 1481908363, 1445210273, 1409528760, 1374830639, 1341084033, 1308258313, 1276324039, 1245252905, 1215017690, 1185592203, 1156951242, 1129070546, 1101926755, 1075497369, 1049760711, 1024695891, 1000282771, 976501934, 953334654, 930762863, 908769128, 887336620, 866449092, 846090856, 826246755, 806902147, 788042881, 769655279, 751726114, 734242598, 717192359, 700563426, 684344218, 668523522, 653090485, 638034597, 623345676, 609013864, 595029604, 581383639, 568066993, 555070965, 542387119, 530007272, 517923489, 506128069, 494613540, 483372654, 472398370, 461683856, 451222478, 441007792, 431033542, 421293647, 411782202, 402493467, 393421865, 384561974, 375908524, 367456390, 359200591, 351136280, 343258743, 335563398, 328045781, 320701555, 313526495, 306516491, 299667543, 292975755, 286437336, 280048596]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1063).prefactor = (5292830785529023/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1063).cutoff/(generalMeanRows 1063).c)).2 =
    (332189929439219/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1063).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1063).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1063).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1063

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1063).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1063).criticalRate j.val*(generalMeanRows 1063).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1063).c*(generalMeanRows 1063).criticalPoint j.val)).2-
      (generalMeanRows 1063).J/2-(generalMeanRows 1063).error (generalMeanGrid j.val)+
      (generalMeanRows 1063).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1063).c)).2-
      (generalMeanRows 1063).J/2-(generalMeanRows 1063).error 4 := by
  have he : (generalMeanRows 1063).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1063) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1063)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1063

/-! Kernel-checked entropy margins for general spectral rectangle 1064. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1064
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6003078722, 5818219727, 5640918702, 5470764295, 5307373941, 5150391334, 4999484166, 4854342108, 4714675002, 4580211232, 4450696261, 4325891308, 4205572146, 4089528016, 3977560640, 3869483313, 3765120090, 3664305025, 3566881487, 3472701525, 3381625289, 3293520494, 3208261927, 3125730991, 3045815290, 2968408234, 2893408682, 2820720610, 2750252797, 2681918539, 2615635383, 2551324877, 2488912335, 2428326623, 2369499959, 2312367719, 2256868265, 2202942778, 2150535103, 2099591607, 2050061040, 2001894411, 1955044864, 1909467573, 1865119628, 1821959945, 1779949163, 1739049567, 1699224996, 1660440771, 1622663620, 1585861608, 1550004073, 1515061565, 1481005786, 1447809535, 1415446659, 1383892003, 1353121358, 1323111428, 1293839778, 1265284800, 1237425675, 1210242338, 1183715443, 1157826333, 1132557007, 1107890097, 1083808834, 1060297027, 1037339038, 1014919756, 993024579, 971639389, 950750536, 930344813, 910409446, 890932070, 871900716, 853303794, 835130079, 817368695, 800009105, 783041095, 766454762, 750240503, 734389005, 718891230, 703738411, 688922037, 674433845, 660265813, 646410149, 632859284, 619605864, 606642743, 593962974, 581559805, 569426670, 557557182, 545945132, 534584476, 523469336, 512593988, 501952865, 491540545, 481351748, 471381335, 461624300, 452075765, 442730981, 433585317, 424634263, 415873423, 407298511, 398905350, 390689867, 382648089, 374776144, 367070253, 359526733]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1064).prefactor = (2564757930271951/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1064).cutoff/(generalMeanRows 1064).c)).2 =
    (188736468634023/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1064).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1064).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1064).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1064

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1064).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1064).criticalRate j.val*(generalMeanRows 1064).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1064).c*(generalMeanRows 1064).criticalPoint j.val)).2-
      (generalMeanRows 1064).J/2-(generalMeanRows 1064).error (generalMeanGrid j.val)+
      (generalMeanRows 1064).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1064).c)).2-
      (generalMeanRows 1064).J/2-(generalMeanRows 1064).error 4 := by
  have he : (generalMeanRows 1064).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1064) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1064)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1064

/-! Kernel-checked entropy margins for general spectral rectangle 1065. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1065
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5786629388, 5597211721, 5415708380, 5241689676, 5074755803, 4914534216, 4760677296, 4612860261, 4470779289, 4334149838, 4202705131, 4076194777, 3954383540, 3837050201, 3723986545, 3614996418, 3509894878, 3408507416, 3310669239, 3216224619, 3125026284, 3036934866, 2951818394, 2869551814, 2790016560, 2713100146, 2638695792, 2566702082, 2497022636, 2429565814, 2364244437, 2300975529, 2239680072, 2180282785, 2122711909, 2066899014, 2012778814, 1960288994, 1909370049, 1859965136, 1812019926, 1765482479, 1720303113, 1676434290, 1633830504, 1592448178, 1552245568, 1513182668, 1475221128, 1438324166, 1402456497, 1367584258, 1333674939, 1300697319, 1268621405, 1237418373, 1207060516, 1177521189, 1148774762, 1120796575, 1093562890, 1067050853, 1041238453, 1016104487, 991628521, 967790857, 944572505, 921955146, 899921111, 878453346, 857535393, 837151358, 817285894, 797924176, 779051877, 760655153, 742720619, 725235334, 708186781, 691562851, 675351828, 659542372, 644123506, 629084602, 614415367, 600105830, 586146331, 572527511, 559240295, 546275888, 533625763, 521281649, 509235524, 497479605, 486006341, 474808404, 463878680, 453210264, 442796450, 432630727, 422706770, 413018437, 403559758, 394324932, 385308324, 376504454, 367907997, 359513773, 351316749, 343312026, 335494842, 327860565, 320404686, 313122821, 306010701, 299064174, 292279197, 285651836, 279178259, 272854736, 266677637]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1065).prefactor = (5318874885607827/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1065).cutoff/(generalMeanRows 1065).c)).2 =
    (348059052061753/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1065).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1065).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1065).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1065

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1065).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1065).criticalRate j.val*(generalMeanRows 1065).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1065).c*(generalMeanRows 1065).criticalPoint j.val)).2-
      (generalMeanRows 1065).J/2-(generalMeanRows 1065).error (generalMeanGrid j.val)+
      (generalMeanRows 1065).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1065).c)).2-
      (generalMeanRows 1065).J/2-(generalMeanRows 1065).error 4 := by
  have he : (generalMeanRows 1065).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1065) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1065)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1065

/-! Kernel-checked entropy margins for general spectral rectangle 1066. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1066
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5918943910, 5736958463, 5562452285, 5395013838, 5234260627, 5079836642, 4931410076, 4788671281, 4651330946, 4519118446, 4391780358, 4269079128, 4150791850, 4036709168, 3926634276, 3820381999, 3717777968, 3618657850, 3522866657, 3430258101, 3340694007, 3254043773, 3170183870, 3088997384, 3010373586, 2934207547, 2860399768, 2788855844, 2719486155, 2652205572, 2586933185, 2523592061, 2462108999, 2402414321, 2344441663, 2288127790, 2233412414, 2180238032, 2128549773, 2078295246, 2029424412, 1981889452, 1935644648, 1890646276, 1846852494, 1804223248, 1762720177, 1722306529, 1682947074, 1644608031, 1607256996, 1570862867, 1535395787, 1500827081, 1467129194, 1434275645, 1402240969, 1371000670, 1340531180, 1310809810, 1281814712, 1253524840, 1225919913, 1198980384, 1172687399, 1147022776, 1121968968, 1097509040, 1073626637, 1050305966, 1027531767, 1005289292, 983564284, 962342955, 941611970, 921358423, 901569826, 882234086, 863339495, 844874712, 826828745, 809190945, 791950988, 775098862, 758624858, 742519556, 726773818, 711378771, 696325805, 681606558, 667212909, 653136969, 639371073, 625907774, 612739830, 599860203, 587262049, 574938712, 562883717, 551090764, 539553723, 528266629, 517223675, 506419208, 495847722, 485503857, 475382391, 465478238, 455786442, 446302173, 437020726, 427937513, 419048064, 410348017, 401833124, 393499238, 385342316, 377358416, 369543690, 361894386, 354406841]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1066).prefactor = (5145045905700011/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1066).cutoff/(generalMeanRows 1066).c)).2 =
    (198730659896221/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1066).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1066).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1066).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1066

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1066).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1066).criticalRate j.val*(generalMeanRows 1066).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1066).c*(generalMeanRows 1066).criticalPoint j.val)).2-
      (generalMeanRows 1066).J/2-(generalMeanRows 1066).error (generalMeanGrid j.val)+
      (generalMeanRows 1066).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1066).c)).2-
      (generalMeanRows 1066).J/2-(generalMeanRows 1066).error 4 := by
  have he : (generalMeanRows 1066).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1066) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1066)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1066

/-! Kernel-checked entropy margins for general spectral rectangle 1067. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1067
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6122891597, 5934635520, 5754116423, 5580908587, 5414616340, 5254871404, 5101330537, 4953673425, 4811600786, 4674832670, 4543106923, 4416177805, 4293814729, 4175801127, 4061933409, 3952020022, 3845880588, 3743345111, 3644253263, 3548453715, 3455803531, 3366167610, 3279418166, 3195434255, 3114101336, 3035310861, 2958959904, 2884950808, 2813190864, 2743592008, 2676070547, 2610546892, 2546945322, 2485193758, 2425223550, 2366969282, 2310368591, 2255361992, 2201892723, 2149906587, 2099351822, 2050178960, 2002340710, 1955791840, 1910489065, 1866390953, 1823457820, 1781651648, 1740935994, 1701275912, 1662637880, 1624989727, 1588300566, 1552540734, 1517681727, 1483696151, 1450557663, 1418240925, 1386721555, 1355976082, 1325981906, 1296717256, 1268161154, 1240293375, 1213094419, 1186545476, 1160628395, 1135325656, 1110620343, 1086496117, 1062937193, 1039928314, 1017454732, 995502185, 974056877, 953105458, 932635009, 912633023, 893087386, 873986365, 855318593, 837073051, 819239061, 801806265, 784764620, 768104382, 751816096, 735890586, 720318943, 705092518, 690202910, 675641959, 661401735, 647474534, 633852865, 620529448, 607497203, 594749243, 582278871, 570079571, 558145001, 546468991, 535045533, 523868778, 512933033, 502232752, 491762533, 481517114, 471491370, 461680304, 452079048, 442682858, 433487106, 424487285, 415678995, 407057950, 398619968, 390360968, 382276972, 374364097, 366618556]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1067).prefactor = (665290946000257/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1067).cutoff/(generalMeanRows 1067).c)).2 =
    (198730659896221/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1067).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1067).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1067).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1067

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1067).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1067).criticalRate j.val*(generalMeanRows 1067).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1067).c*(generalMeanRows 1067).criticalPoint j.val)).2-
      (generalMeanRows 1067).J/2-(generalMeanRows 1067).error (generalMeanGrid j.val)+
      (generalMeanRows 1067).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1067).c)).2-
      (generalMeanRows 1067).J/2-(generalMeanRows 1067).error 4 := by
  have he : (generalMeanRows 1067).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1067) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1067)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1067

/-! Kernel-checked entropy margins for general spectral rectangle 1068. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1068
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6428147741, 6233028119, 6045894157, 5866306074, 5693855170, 5528161081, 5368869339, 5215649189, 5068191627, 4926207638, 4789426615, 4657594916, 4530474569, 4407842095, 4289487429, 4175212952, 4064832589, 3958171002, 3855062837, 3755352042, 3658891237, 3565541134, 3475170003, 3387653180, 3302872614, 3220716444, 3141078612, 3063858500, 2988960600, 2916294196, 2845773084, 2777315295, 2710842853, 2646281535, 2583560657, 2522612874, 2463373984, 2405782756, 2349780763, 2295312229, 2242323880, 2190764809, 2140586354, 2091741971, 2044187124, 1997879184, 1952777325, 1908842431, 1866037012, 1824325117, 1783672262, 1744045352, 1705412613, 1667743529, 1631008780, 1595180183, 1560230639, 1526134080, 1492865423, 1460400521, 1428716119, 1397789817, 1367600027, 1338125939, 1309347485, 1281245304, 1253800713, 1226995679, 1200812785, 1175235210, 1150246700, 1125831543, 1101974548, 1078661026, 1055876761, 1033608001, 1011841431, 990564159, 969763699, 949427953, 929545200, 910104075, 891093561, 872502974, 854321947, 836540423, 819148641, 802137125, 785496675, 769218353, 753293479, 737713619, 722470576, 707556381, 692963288, 678683764, 664710482, 651036313, 637654323, 624557763, 611740063, 599194828, 586915831, 574897009, 563132454, 551616413, 540343281, 529307595, 518504031, 507927401, 497572645, 487434832, 477509151, 467790912, 458275540, 448958573, 439835656, 430902540, 422155080, 413589230, 405201041]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1068).prefactor = (550571778372901/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1068).cutoff/(generalMeanRows 1068).c)).2 =
    (403343689695511/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1068).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1068).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1068).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1068

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1068).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1068).criticalRate j.val*(generalMeanRows 1068).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1068).c*(generalMeanRows 1068).criticalPoint j.val)).2-
      (generalMeanRows 1068).J/2-(generalMeanRows 1068).error (generalMeanGrid j.val)+
      (generalMeanRows 1068).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1068).c)).2-
      (generalMeanRows 1068).J/2-(generalMeanRows 1068).error 4 := by
  have he : (generalMeanRows 1068).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1068) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1068)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1068

/-! Kernel-checked entropy margins for general spectral rectangle 1069. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1069
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6849917379, 6647392142, 6453089117, 6266554562, 6087366886, 5915133816, 5749489863, 5590094061, 5436627938, 5288793692, 5146312550, 5008923276, 4876380832, 4748455154, 4624930043, 4505602149, 4390280056, 4278783431, 4170942251, 4066596096, 3965593499, 3867791341, 3773054303, 3681254355, 3592270287, 3505987271, 3422296463, 3341094624, 3262283781, 3185770899, 3111467588, 3039289822, 2969157679, 2900995106, 2834729690, 2770292447, 2707617633, 2646642552, 2587307395, 2529555070, 2473331061, 2418583281, 2365261946, 2313319445, 2262710232, 2213390711, 2165319136, 2118455517, 2072761526, 2028200415, 1984736935, 1942337259, 1900968915, 1860600715, 1821202696, 1782746056, 1745203101, 1708547193, 1672752695, 1637794929, 1603650130, 1570295401, 1537708675, 1505868678, 1474754893, 1444347525, 1414627467, 1385576275, 1357176134, 1329409835, 1302260743, 1275712780, 1249750394, 1224358544, 1199522672, 1175228689, 1151462952, 1128212247, 1105463772, 1083205122, 1061424270, 1040109554, 1019249665, 998833630, 978850800, 959290839, 940143712, 921399673, 903049256, 885083260, 867492749, 850269030, 833403656, 816888411, 800715301, 784876552, 769364596, 754172069, 739291802, 724716815, 710440308, 696455661, 682756423, 669336308, 656189190, 643309099, 630690215, 618326862, 606213505, 594344748, 582715325, 571320100, 560154060, 549212314, 538490089, 527982725, 517685673, 507594492, 497704844, 488012494, 478513305]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1069).prefactor = (5695427033899951/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1069).cutoff/(generalMeanRows 1069).c)).2 =
    (415213265250893/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1069).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1069).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1069).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1069

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1069).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1069).criticalRate j.val*(generalMeanRows 1069).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1069).c*(generalMeanRows 1069).criticalPoint j.val)).2-
      (generalMeanRows 1069).J/2-(generalMeanRows 1069).error (generalMeanGrid j.val)+
      (generalMeanRows 1069).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1069).c)).2-
      (generalMeanRows 1069).J/2-(generalMeanRows 1069).error 4 := by
  have he : (generalMeanRows 1069).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1069) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1069)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1069

/-! Kernel-checked entropy margins for general spectral rectangle 1070. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1070
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7192299270, 6982495604, 6781176729, 6587873849, 6402151432, 6223604275, 6051854884, 5886551133, 5727364162, 5573986495, 5426130330, 5283526008, 5145920617, 5013076729, 4884771252, 4760794383, 4640948649, 4525048040, 4412917200, 4304390699, 4199312359, 4097534629, 3998918016, 3903330561, 3810647346, 3720750049, 3633526526, 3548870423, 3466680822, 3386861904, 3309322645, 3233976526, 3160741264, 3089538568, 3020293902, 2952936270, 2887398014, 2823614626, 2761524566, 2701069105, 2642192164, 2584840169, 2528961919, 2474508454, 2421432940, 2369690551, 2319238369, 2270035281, 2222041888, 2175220417, 2129534636, 2084949779, 2041432472, 1998950665, 1957473563, 1916971569, 1877416225, 1838780157, 1801037021, 1764161459, 1728129048, 1692916261, 1658500422, 1624859668, 1591972916, 1559819819, 1528380745, 1497636734, 1467569476, 1438161280, 1409395049, 1381254249, 1353722895, 1326785517, 1300427147, 1274633295, 1249389926, 1224683450, 1200500694, 1176828895, 1153655675, 1130969033, 1108757325, 1087009255, 1065713858, 1044860488, 1024438809, 1004438779, 984850643, 965664921, 946872397, 928464111, 910431350, 892765639, 875458731, 858502602, 841889442, 825611647, 809661814, 794032730, 778717373, 763708898, 749000637, 734586091, 720458923, 706612957, 693042168, 679740682, 666702768, 653922835, 641395428, 629115223, 617077024, 605275760, 593706478, 582364343, 571244633, 560342737, 549654149, 539174470, 528899399]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1070).prefactor = (5891673052029967/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1070).cutoff/(generalMeanRows 1070).c)).2 =
    (210600653547759/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1070).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1070).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1070).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1070

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1070).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1070).criticalRate j.val*(generalMeanRows 1070).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1070).c*(generalMeanRows 1070).criticalPoint j.val)).2-
      (generalMeanRows 1070).J/2-(generalMeanRows 1070).error (generalMeanGrid j.val)+
      (generalMeanRows 1070).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1070).c)).2-
      (generalMeanRows 1070).J/2-(generalMeanRows 1070).error 4 := by
  have he : (generalMeanRows 1070).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1070) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1070)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1070

/-! Kernel-checked entropy margins for general spectral rectangle 1071. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1071
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7537316366, 7323432890, 7118135537, 6920948601, 6731430228, 6549169420, 6373783369, 6204915073, 6042231195, 5885420145, 5734190342, 5588268648, 5447398955, 5311340894, 5179868666, 5052769976, 4929845058, 4810905791, 4695774876, 4584285096, 4476278625, 4371606397, 4270127527, 4171708772, 4076224036, 3983553911, 3893585257, 3806210803, 3721328790, 3638842626, 3558660578, 3480695475, 3404864439, 3331088629, 3259293008, 3189406122, 3121359892, 3055089423, 2990532826, 2927631048, 2866327716, 2806568987, 2748303415, 2691481815, 2636057147, 2581984400, 2529220484, 2477724129, 2427455794, 2378377573, 2330453117, 2283647549, 2237927393, 2193260506, 2149616008, 2106964222, 2065276617, 2024525747, 1984685206, 1945729574, 1907634371, 1870376015, 1833931776, 1798279743, 1763398780, 1729268497, 1695869211, 1663181918, 1631188262, 1599870505, 1569211504, 1539194681, 1509804001, 1481023949, 1452839509, 1425236141, 1398199762, 1371716729, 1345773819, 1320358214, 1295457483, 1271059567, 1247152768, 1223725729, 1200767425, 1178267149, 1156214501, 1134599376, 1113411953, 1092642682, 1072282280, 1052321717, 1032752206, 1013565200, 994752378, 976305638, 958217093, 940479059, 923084054, 906024784, 889294142, 872885201, 856791207, 841005574, 825521878, 810333854, 795435389, 780820516, 766483413, 752418398, 738619921, 725082566, 711801040, 698770175, 685984924, 673440354, 661131646, 649054089, 637203079, 625574117, 614162803]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1071).prefactor = (5992317435230421/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1071).cutoff/(generalMeanRows 1071).c)).2 =
    (108321511577647/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1071).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1071).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1071).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1071

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1071).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1071).criticalRate j.val*(generalMeanRows 1071).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1071).c*(generalMeanRows 1071).criticalPoint j.val)).2-
      (generalMeanRows 1071).J/2-(generalMeanRows 1071).error (generalMeanGrid j.val)+
      (generalMeanRows 1071).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1071).c)).2-
      (generalMeanRows 1071).J/2-(generalMeanRows 1071).error 4 := by
  have he : (generalMeanRows 1071).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1071) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1071)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1071

/-! Kernel-checked entropy margins for general spectral rectangle 1072. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1072
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7094123517, 6889260933, 6692373831, 6503044368, 6320883470, 6145528272, 5976639852, 5813901207, 5657015439, 5505704134, 5359705904, 5218775071, 5082680473, 4951204394, 4824141579, 4701298347, 4582491781, 4467548982, 4356306392, 4248609174, 4144310637, 4043271711, 3945360465, 3850451654, 3758426312, 3669171367, 3582579286, 3498547747, 3416979334, 3337781253, 3260865068, 3186146455, 3113544971, 3042983841, 2974389756, 2907692688, 2842825712, 2779724843, 2718328882, 2658579269, 2600419949, 2543797245, 2488659736, 2434958145, 2382645232, 2331675693, 2282006068, 2233594648, 2186401395, 2140387858, 2095517102, 2051753634, 2009063337, 1967413404, 1926772284, 1887109618, 1848396187, 1810603865, 1773705564, 1737675191, 1702487605, 1668118575, 1634544739, 1601743567, 1569693328, 1538373052, 1507762501, 1477842136, 1448593090, 1419997138, 1392036673, 1364694678, 1337954705, 1311800848, 1286217727, 1261190462, 1236704653, 1212746367, 1189302113, 1166358828, 1143903861, 1121924956, 1100410236, 1079348193, 1058727667, 1038537839, 1018768218, 999408623, 980449180, 961880305, 943692694, 925877315, 908425399, 891328425, 874578120, 858166442, 842085577, 826327929, 810886113, 795752949, 780921453, 766384831, 752136474, 738169950, 724478999, 711057528, 697899603, 684999447, 672351434, 659950083, 647790055, 635866146, 624173286, 612706532, 601461067, 590432192, 579615327, 569006005, 558599867, 548392662, 538380242]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1072).prefactor = (1320329404766509/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1072).cutoff/(generalMeanRows 1072).c)).2 =
    (335509933825671/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1072).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1072).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1072).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1072

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1072).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1072).criticalRate j.val*(generalMeanRows 1072).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1072).c*(generalMeanRows 1072).criticalPoint j.val)).2-
      (generalMeanRows 1072).J/2-(generalMeanRows 1072).error (generalMeanGrid j.val)+
      (generalMeanRows 1072).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1072).c)).2-
      (generalMeanRows 1072).J/2-(generalMeanRows 1072).error 4 := by
  have he : (generalMeanRows 1072).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1072) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1072)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1072

/-! Kernel-checked entropy margins for general spectral rectangle 1073. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1073
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6756077899, 6561062462, 6373696107, 6193574016, 6020319362, 5853580836, 5693030436, 5538361505, 5389286965, 5245537744, 5106861348, 4973020583, 4843792399, 4718966829, 4598346047, 4481743489, 4368983066, 4259898440, 4154332355, 4052136037, 3953168630, 3857296682, 3764393673, 3674339578, 3587020462, 3502328106, 3420159660, 3340417325, 3263008051, 3187843260, 3114838589, 3043913650, 2974991804, 2907999952, 2842868340, 2779530375, 2717922454, 2657983805, 2599656334, 2542884487, 2487615115, 2433797351, 2381382493, 2330323893, 2280576854, 2232098535, 2184847855, 2138785408, 2093873383, 2050075485, 2007356862, 1965684038, 1925024846, 1885348368, 1846624877, 1808825779, 1771923565, 1735891760, 1700704873, 1666338360, 1632768573, 1599972728, 1567928861, 1536615797, 1506013111, 1476101102, 1446860753, 1418273712, 1390322255, 1362989266, 1336258209, 1310113103, 1284538501, 1259519468, 1235041559, 1211090800, 1187653670, 1164717083, 1142268367, 1120295252, 1098785855, 1077728660, 1057112510, 1036926587, 1017160405, 997803794, 978846888, 960280117, 942094191, 924280094, 906829074, 889732629, 872982504, 856570677, 840489353, 824730959, 809288129, 794153703, 779320720, 764782406, 750532171, 736563605, 722870468, 709446685, 696286344, 683383685, 670733100, 658329127, 646166443, 634239861, 622544328, 611074915, 599826820, 588795360, 577975967, 567364186, 556955672, 546746185, 536731588, 526907844, 517271013]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1073).prefactor = (2555795165954469/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1073).cutoff/(generalMeanRows 1073).c)).2 =
    (70671955298169/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1073).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1073).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1073).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1073

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1073).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1073).criticalRate j.val*(generalMeanRows 1073).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1073).c*(generalMeanRows 1073).criticalPoint j.val)).2-
      (generalMeanRows 1073).J/2-(generalMeanRows 1073).error (generalMeanGrid j.val)+
      (generalMeanRows 1073).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1073).c)).2-
      (generalMeanRows 1073).J/2-(generalMeanRows 1073).error 4 := by
  have he : (generalMeanRows 1073).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1073) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1073)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1073

/-! Kernel-checked entropy margins for general spectral rectangle 1074. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1074
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6591697650, 6388728293, 6193872485, 6006702756, 5826821013, 5653855946, 5487460717, 5327310902, 5173102646, 5024551014, 4881388498, 4743363675, 4610239997, 4481794685, 4357817732, 4238110992, 4122487350, 4010769962, 3902791561, 3798393818, 3697426757, 3599748218, 3505223356, 3413724186, 3325129156, 3239322757, 3156195162, 3075641880, 2997563452, 2921865156, 2848456734, 2777252142, 2708169311, 2641129932, 2576059245, 2512885849, 2451541522, 2391961051, 2334082074, 2277844933, 2223192532, 2170070209, 2118425608, 2068208568, 2019371013, 1971866844, 1925651848, 1880683606, 1836921402, 1794326146, 1752860295, 1712487781, 1673173942, 1634885457, 1597590281, 1561257594, 1525857739, 1491362172, 1457743412, 1424974995, 1393031427, 1361888145, 1331521471, 1301908580, 1273027461, 1244856879, 1217376349, 1190566098, 1164407040, 1138880745, 1113969412, 1089655845, 1065923427, 1042756098, 1020138329, 998055107, 976491910, 955434687, 934869845, 914784225, 895165090, 876000105, 857277324, 838985177, 821112451, 803648281, 786582136, 769903804, 753603385, 737671277, 722098163, 706875006, 691993035, 677443737, 663218848, 649310343, 635710430, 622411539, 609406319, 596687624, 584248511, 572082233, 560182229, 548542122, 537155709, 526016958, 515120002, 504459133, 494028797, 483823589, 473838248, 464067655, 454506823, 445150898, 435995155, 427034988, 418265914, 409683564, 401283683, 393062121, 385014838]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1074).prefactor = (268163465840821/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1074).cutoff/(generalMeanRows 1074).c)).2 =
    (322009246606769/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1074).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1074).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1074).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1074

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1074).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1074).criticalRate j.val*(generalMeanRows 1074).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1074).c*(generalMeanRows 1074).criticalPoint j.val)).2-
      (generalMeanRows 1074).J/2-(generalMeanRows 1074).error (generalMeanGrid j.val)+
      (generalMeanRows 1074).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1074).c)).2-
      (generalMeanRows 1074).J/2-(generalMeanRows 1074).error 4 := by
  have he : (generalMeanRows 1074).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1074) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1074)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1074

/-! Kernel-checked entropy margins for general spectral rectangle 1075. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1075
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6603237037, 6409281193, 6223024176, 6044054843, 5871990590, 5706474832, 5547174754, 5393779315, 5245997448, 5103556453, 4966200546, 4833689552, 4705797720, 4582312649, 4463034316, 4347774182, 4236354386, 4128607004, 4024373369, 3923503447, 3825855269, 3731294403, 3639693467, 3550931684, 3464894469, 3381473045, 3300564085, 3222069390, 3145895580, 3071953808, 3000159500, 2930432107, 2862694874, 2796874629, 2732901582, 2670709136, 2610233716, 2551414602, 2494193776, 2438515780, 2384327579, 2331578438, 2280219796, 2230205161, 2181490002, 2134031648, 2087789199, 2042723434, 1998796730, 1955972984, 1914217539, 1873497114, 1833779736, 1795034685, 1757232425, 1720344557, 1684343763, 1649203754, 1614899228, 1581405821, 1548700064, 1516759349, 1485561885, 1455086662, 1425313420, 1396222616, 1367795389, 1340013536, 1312859480, 1286316247, 1260367436, 1234997201, 1210190222, 1185931689, 1162207276, 1139003125, 1116305826, 1094102400, 1072380279, 1051127293, 1030331653, 1009981937, 990067075, 970576335, 951499313, 932825916, 914546354, 896651129, 879131022, 861977082, 845180621, 828733198, 812626618, 796852914, 781404347, 766273393, 751452739, 736935272, 722714076, 708782422, 695133763, 681761729, 668660119, 655822898, 643244189, 630918268, 618839562, 607002640, 595402211, 584033121, 572890345, 561968985, 551264266, 540771531, 530486242, 520403968, 510520390, 500831294, 491332567, 482020196, 472890263]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1075).prefactor = (161921738693773/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1075).cutoff/(generalMeanRows 1075).c)).2 =
    (363292536665959/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1075).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1075).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1075).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1075

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1075).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1075).criticalRate j.val*(generalMeanRows 1075).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1075).c*(generalMeanRows 1075).criticalPoint j.val)).2-
      (generalMeanRows 1075).J/2-(generalMeanRows 1075).error (generalMeanGrid j.val)+
      (generalMeanRows 1075).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1075).c)).2-
      (generalMeanRows 1075).J/2-(generalMeanRows 1075).error 4 := by
  have he : (generalMeanRows 1075).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1075) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1075)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1075

/-! Kernel-checked entropy margins for general spectral rectangle 1076. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1076
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6235671890, 6035751147, 5843994884, 5659969175, 5483269951, 5313520373, 5150368491, 4993485157, 4842562160, 4697310539, 4557459078, 4422752939, 4292952425, 4167831865, 4047178592, 3930792017, 3818482783, 3710071991, 3605390493, 3504278239, 3406583682, 3312163227, 3220880722, 3132606995, 3047219416, 2964601498, 2884642529, 2807237222, 2732285401, 2659691699, 2589365283, 2521219598, 2455172121, 2391144141, 2329060547, 2268849634, 2210442914, 2153774949, 2098783188, 2045407816, 1993591608, 1943279803, 1894419970, 1846961898, 1800857477, 1756060600, 1712527060, 1670214459, 1629082121, 1589091006, 1550203635, 1512384014, 1475597565, 1439811062, 1404992562, 1371111355, 1338137900, 1306043777, 1274801633, 1244385137, 1214768934, 1185928601, 1157840609, 1130482281, 1103831755, 1077867954, 1052570546, 1027919920, 1003897147, 980483960, 957662722, 935416399, 913728541, 892583251, 871965170, 851859449, 832251734, 813128143, 794475249, 776280062, 758530012, 741212933, 724317047, 707830951, 691743601, 676044298, 660722677, 645768697, 631172621, 616925013, 603016724, 589438882, 576182881, 563240371, 550603254, 538263668, 526213984, 514446796, 502954913, 491731353, 480769333, 470062267, 459603755, 449387577, 439407692, 429658225, 420133468, 410827869, 401736032, 392852707, 384172790, 375691316, 367403453, 359304502, 351389888, 343655161, 336095988, 328708151, 321487546, 314430174, 307532144]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1076).prefactor = (5415502222660643/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1076).cutoff/(generalMeanRows 1076).c)).2 =
    (64146584449433/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1076).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1076).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1076).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1076

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1076).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1076).criticalRate j.val*(generalMeanRows 1076).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1076).c*(generalMeanRows 1076).criticalPoint j.val)).2-
      (generalMeanRows 1076).J/2-(generalMeanRows 1076).error (generalMeanGrid j.val)+
      (generalMeanRows 1076).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1076).c)).2-
      (generalMeanRows 1076).J/2-(generalMeanRows 1076).error 4 := by
  have he : (generalMeanRows 1076).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1076) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1076)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1076

/-! Kernel-checked entropy margins for general spectral rectangle 1077. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1077
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6383281720, 6191733471, 6007888456, 5831331513, 5661676420, 5498563347, 5341656582, 5190642499, 5045227742, 4905137586, 4770114470, 4639916666, 4514317076, 4393102140, 4276070845, 4163033822, 4053812521, 3948238454, 3846152511, 3747404319, 3651851666, 3559359959, 3469801736, 3383056210, 3299008843, 3217550960, 3138579390, 3061996127, 2987708023, 2915626498, 2845667269, 2777750105, 2711798591, 2647739910, 2585504642, 2525026572, 2466242514, 2409092148, 2353517857, 2299464589, 2246879718, 2195712912, 2145916018, 2097442948, 2050249569, 2004293607, 1959534551, 1915933565, 1873453403, 1832058333, 1791714063, 1752387666, 1714047518, 1676663238, 1640205622, 1604646594, 1569959148, 1536117304, 1503096053, 1470871320, 1439419918, 1408719507, 1378748560, 1349486321, 1320912776, 1293008620, 1265755223, 1239134603, 1213129399, 1187722844, 1162898739, 1138641429, 1114935783, 1091767170, 1069121438, 1046984898, 1025344300, 1004186822, 983500047, 963271951, 943490884, 924145560, 905225039, 886718715, 868616306, 850907838, 833583633, 816634303, 800050735, 783824083, 767945755, 752407409, 737200942, 722318477, 707752364, 693495165, 679539647, 665878779, 652505723, 639413825, 626596615, 614047793, 601761230, 589730958, 577951169, 566416205, 555120555, 544058855, 533225874, 522616519, 512225824, 502048951, 492081182, 482317919, 472754677, 463387084, 454210873, 445221885, 436416060, 427789437, 419338153]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1077).prefactor = (5223606393455581/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1077).cutoff/(generalMeanRows 1077).c)).2 =
    (372093351004181/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1077).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1077).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1077).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1077

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1077).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1077).criticalRate j.val*(generalMeanRows 1077).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1077).c*(generalMeanRows 1077).criticalPoint j.val)).2-
      (generalMeanRows 1077).J/2-(generalMeanRows 1077).error (generalMeanGrid j.val)+
      (generalMeanRows 1077).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1077).c)).2-
      (generalMeanRows 1077).J/2-(generalMeanRows 1077).error 4 := by
  have he : (generalMeanRows 1077).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1077) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1077)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1077

/-! Kernel-checked entropy margins for general spectral rectangle 1078. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1078
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6094792522, 5897844085, 5709019057, 5527881190, 5354024416, 5187070199, 5026665168, 4872479008, 4724202573, 4581546181, 4444238091, 4312023115, 4184661370, 4061927142, 3943607852, 3829503122, 3719423908, 3613191722, 3510637910, 3411602992, 3315936056, 3223494201, 3134142020, 3047751127, 2964199716, 2883372158, 2805158621, 2729454722, 2656161203, 2585183630, 2516432111, 2449821036, 2385268831, 2322697735, 2262033583, 2203205609, 2146146262, 2090791028, 2037078272, 1984949083, 1934347129, 1885218524, 1837511703, 1791177299, 1746168037, 1702438622, 1659945648, 1618647494, 1578504248, 1539477614, 1501530840, 1464628640, 1428737126, 1393823744, 1359857205, 1326807435, 1294645512, 1263343614, 1232874974, 1203213826, 1174335364, 1146215699, 1118831815, 1092161537, 1066183488, 1040877060, 1016222376, 992200263, 968792219, 945980387, 923747527, 902076992, 880952702, 860359120, 840281233, 820704529, 801614976, 782999005, 764843492, 747135737, 729863451, 713014742, 696578092, 680542351, 664896719, 649630733, 634734256, 620197465, 606010835, 592165134, 578651410, 565460981, 552585424, 540016567, 527746482, 515767472, 504072066, 492653014, 481503270, 470615997, 459984551, 449602477, 439463505, 429561540, 419890660, 410445108, 401219286, 392207753, 383405216, 374806529, 366406683, 358200810, 350184169, 342352151, 334700267, 327224149, 319919548, 312782322, 305808443, 298993988, 292335134]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1078).prefactor = (5441052114046083/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1078).cutoff/(generalMeanRows 1078).c)).2 =
    (42060159901913/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1078).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1078).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1078).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1078

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1078).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1078).criticalRate j.val*(generalMeanRows 1078).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1078).c*(generalMeanRows 1078).criticalPoint j.val)).2-
      (generalMeanRows 1078).J/2-(generalMeanRows 1078).error (generalMeanGrid j.val)+
      (generalMeanRows 1078).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1078).c)).2-
      (generalMeanRows 1078).J/2-(generalMeanRows 1078).error 4 := by
  have he : (generalMeanRows 1078).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1078) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1078)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1078

/-! Kernel-checked entropy margins for general spectral rectangle 1079. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1079
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6198778751, 6010484159, 5829838876, 5656426427, 5489859554, 5329777640, 5175844414, 5027745903, 4885188592, 4747897768, 4615616037, 4488101975, 4365128914, 4246483832, 4131966350, 4021387821, 3914570487, 3811346722, 3711558326, 3615055890, 3521698199, 3431351693, 3343889967, 3259193308, 3177148271, 3097647283, 3020588276, 2945874354, 2873413472, 2803118151, 2734905201, 2668695472, 2604413619, 2541987879, 2481349870, 2422434400, 2365179285, 2309525184, 2255415446, 2202795957, 2151615008, 2101823165, 2053373146, 2006219713, 1960319559, 1915631213, 1872114945, 1829732674, 1788447890, 1748225570, 1709032111, 1670835252, 1633604015, 1597308639, 1561920524, 1527412173, 1493757144, 1460929994, 1428906238, 1397662305, 1367175491, 1337423923, 1308386523, 1280042969, 1252373662, 1225359698, 1198982832, 1173225453, 1148070556, 1123501714, 1099503059, 1076059252, 1053155464, 1030777355, 1008911056, 987543143, 966660628, 946250934, 926301882, 906801676, 887738888, 869102440, 850881595, 833065941, 815645383, 798610125, 781950662, 765657771, 749722497, 734136147, 718890277, 703976685, 689387402, 675114685, 661151008, 647489053, 634121704, 621042044, 608243341, 595719048, 583462793, 571468375, 559729758, 548241066, 536996576, 525990718, 515218063, 504673325, 494351351, 484247123, 474355748, 464672458, 455192604, 445911655, 436825191, 427928903, 419218586, 410690140, 402339566, 394162960, 386156514]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1079).prefactor = (2620467953117103/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1079).cutoff/(generalMeanRows 1079).c)).2 =
    (9648798674591/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1079).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1079).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1079).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1079

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1079).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1079).criticalRate j.val*(generalMeanRows 1079).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1079).c*(generalMeanRows 1079).criticalPoint j.val)).2-
      (generalMeanRows 1079).J/2-(generalMeanRows 1079).error (generalMeanGrid j.val)+
      (generalMeanRows 1079).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1079).c)).2-
      (generalMeanRows 1079).J/2-(generalMeanRows 1079).error 4 := by
  have he : (generalMeanRows 1079).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1079) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1079)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1079

/-! Kernel-checked entropy margins for general spectral rectangle 1080. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1080
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5900341421, 5707497233, 5522694783, 5345497596, 5175499579, 5012322354, 4855612881, 4705041331, 4560299183, 4421097510, 4287165437, 4158248743, 4034108603, 3914520437, 3799272872, 3688166788, 3581014455, 3477638737, 3377872366, 3281557275, 3188543987, 3098691048, 3011864511, 2927937451, 2846789528, 2768306570, 2692380199, 2618907475, 2547790569, 2478936461, 2412256655, 2347666918, 2285087032, 2224440568, 2165654670, 2108659854, 2053389828, 1999781309, 1947773864, 1897309759, 1848333809, 1800793248, 1754637602, 1709818568, 1666289903, 1624007322, 1582928393, 1543012451, 1504220503, 1466515152, 1429860515, 1394222150, 1359566988, 1325863265, 1293080463, 1261189250, 1230161425, 1199969864, 1170588472, 1141992138, 1114156686, 1087058838, 1060676169, 1034987073, 1009970725, 985607050, 961876686, 938760956, 916241841, 894301946, 872924482, 852093233, 831792537, 812007263, 792722786, 773924972, 755600154, 737735113, 720317064, 703333637, 686772860, 670623145, 654873272, 639512375, 624529932, 609915747, 595659941, 581752938, 568185458, 554948502, 542033344, 529431519, 517134816, 505135269, 493425148, 481996948, 470843385, 459957387, 449332087, 438960814, 428837089, 418954618, 409307284, 399889145, 390694424, 381717505, 372952928, 364395387, 356039718, 347880902, 339914056, 332134428, 324537398, 317118468, 309873261, 302797518, 295887093, 289137951, 282546161, 276107900, 269819440]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1080).prefactor = (5442810421700479/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1080).cutoff/(generalMeanRows 1080).c)).2 =
    (21947864431139/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1080).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1080).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1080).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1080

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1080).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1080).criticalRate j.val*(generalMeanRows 1080).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1080).c*(generalMeanRows 1080).criticalPoint j.val)).2-
      (generalMeanRows 1080).J/2-(generalMeanRows 1080).error (generalMeanGrid j.val)+
      (generalMeanRows 1080).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1080).c)).2-
      (generalMeanRows 1080).J/2-(generalMeanRows 1080).error 4 := by
  have he : (generalMeanRows 1080).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1080) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1080)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1080

/-! Kernel-checked entropy margins for general spectral rectangle 1081. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1081
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6007640334, 5823401147, 5646712361, 5477158538, 5314353607, 5157938273, 5007577707, 4862959483, 4723791727, 4589801448, 4460733038, 4336346918, 4216418308, 4100736111, 3989101903, 3881329005, 3777241642, 3676674171, 3579470379, 3485482829, 3394572271, 3306607089, 3221462803, 3139021599, 3059171901, 2981807978, 2906829569, 2834141547, 2763653606, 2695279961, 2628939080, 2564553430, 2502049241, 2441356286, 2382407675, 2325139665, 2269491481, 2215405151, 2162825346, 2111699238, 2061976359, 2013608478, 1966549477, 1920755239, 1876183544, 1832793969, 1790547792, 1749407909, 1709338748, 1670306193, 1632277509, 1595221277, 1559107325, 1523906669, 1489591455, 1456134905, 1423511265, 1391695756, 1360664531, 1330394626, 1300863926, 1272051121, 1243935671, 1216497774, 1189718329, 1163578905, 1138061715, 1113149587, 1088825935, 1065074735, 1041880503, 1019228269, 997103560, 975492375, 954381168, 933756829, 913606665, 893918386, 874680088, 855880238, 837507656, 819551508, 802001288, 784846805, 768078175, 751685807, 735660392, 719992894, 704674538, 689696802, 675051410, 660730319, 646725713, 633029996, 619635783, 606535893, 593723342, 581191336, 568933268, 556942706, 545213392, 533739234, 522514302, 511532819, 500789164, 490277860, 479993570, 469931096, 460085374, 450451468, 441024567, 431799981, 422773139, 413939583, 405294967, 396835050, 388555699, 380452880, 372522659, 364761196, 357164745]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1081).prefactor = (81816922758559/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1081).cutoff/(generalMeanRows 1081).c)).2 =
    (25115499223157/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1081).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1081).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1081).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1081

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1081).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1081).criticalRate j.val*(generalMeanRows 1081).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1081).c*(generalMeanRows 1081).criticalPoint j.val)).2-
      (generalMeanRows 1081).J/2-(generalMeanRows 1081).error (generalMeanGrid j.val)+
      (generalMeanRows 1081).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1081).c)).2-
      (generalMeanRows 1081).J/2-(generalMeanRows 1081).error 4 := by
  have he : (generalMeanRows 1081).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1081) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1081)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1081

/-! Kernel-checked entropy margins for general spectral rectangle 1082. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1082
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6222437499, 6031611024, 5848604908, 5672988858, 5504363000, 5342355192, 5186618634, 5036829731, 4892686171, 4753905203, 4620222081, 4491388660, 4367172123, 4247353825, 4131728248, 4020102038, 3912293135, 3808129975, 3707450759, 3610102778, 3515941804, 3424831515, 3336642980, 3251254173, 3168549530, 3088419537, 3010760349, 2935473441, 2862465274, 2791646997, 2722934164, 2656246470, 2591507507, 2528644536, 2467588276, 2408272705, 2350634877, 2294614744, 2240155001, 2187200930, 2135700259, 2085603033, 2036861484, 1989429919, 1943264608, 1898323682, 1854567036, 1811956237, 1770454443, 1730026318, 1690637957, 1652256816, 1614851646, 1578392426, 1542850306, 1508197551, 1474407485, 1441454445, 1409313729, 1377961554, 1347375013, 1317532035, 1288411346, 1259992434, 1232255516, 1205181503, 1178751973, 1152949136, 1127755816, 1103155416, 1079131897, 1055669756, 1032754000, 1010370129, 988504111, 967142369, 946271756, 925879543, 905953399, 886481379, 867451904, 848853752, 830676041, 812908217, 795540042, 778561581, 761963193, 745735519, 729869470, 714356221, 699187198, 684354070, 669848744, 655663350, 641790240, 628221976, 614951325, 601971251, 589274908, 576855635, 564706951, 552822546, 541196277, 529822163, 518694380, 507807254, 497155259, 486733012, 476535266, 466556909, 456792959, 447238557, 437888970, 428739579, 419785882, 411023490, 402448119, 394055592, 385841834, 377802867, 369934813]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1082).prefactor = (2711750557378687/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1082).cutoff/(generalMeanRows 1082).c)).2 =
    (25115499223157/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1082).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1082).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1082).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1082

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1082).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1082).criticalRate j.val*(generalMeanRows 1082).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1082).c*(generalMeanRows 1082).criticalPoint j.val)).2-
      (generalMeanRows 1082).J/2-(generalMeanRows 1082).error (generalMeanGrid j.val)+
      (generalMeanRows 1082).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1082).c)).2-
      (generalMeanRows 1082).J/2-(generalMeanRows 1082).error 4 := by
  have he : (generalMeanRows 1082).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1082) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1082)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1082

/-! Kernel-checked entropy margins for general spectral rectangle 1083. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1083
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6540215882, 6342181620, 6152228787, 5969912350, 5794818780, 5626563269, 5464787252, 5309156193, 5159357592, 5015099203, 4876107420, 4742125821, 4612913853, 4488245631, 4367908853, 4251703810, 4139442477, 4030947689, 3926052385, 3824598908, 3726438370, 3631430065, 3539440929, 3450345037, 3364023145, 3280362267, 3199255274, 3120600537, 3044301580, 2970266773, 2898409033, 2828645558, 2760897572, 2695090088, 2631151689, 2569014323, 2508613115, 2449886181, 2392774468, 2337221591, 2283173694, 2230579304, 2179389211, 2129556340, 2081035643, 2033783989, 1987760068, 1942924293, 1899238714, 1856666935, 1815174033, 1774726491, 1735292119, 1696839998, 1659340412, 1622764793, 1587085663, 1552276587, 1518312119, 1485167759, 1452819907, 1421245824, 1390423591, 1360332071, 1330950879, 1302260340, 1274241468, 1246875927, 1220146008, 1194034601, 1168525168, 1143601721, 1119248797, 1095451437, 1072195168, 1049465979, 1027250302, 1005534998, 984307341, 963554993, 943266001, 923428771, 904032061, 885064967, 866516907, 848377612, 830637114, 813285733, 796314067, 779712987, 763473619, 747587340, 732045769, 716840758, 701964383, 687408937, 673166922, 659231046, 645594208, 632249501, 619190197, 606409749, 593901779, 581660076, 569678589, 557951425, 546472838, 535237231, 524239148, 513473270, 502934412, 492617516, 482517653, 472630012, 462949902, 453472747, 444194080, 435109544, 426214887, 417505959, 408978709]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1083).prefactor = (224696518687949/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1083).cutoff/(generalMeanRows 1083).c)).2 =
    (407628350486011/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1083).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1083).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1083).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1083

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1083).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1083).criticalRate j.val*(generalMeanRows 1083).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1083).c*(generalMeanRows 1083).criticalPoint j.val)).2-
      (generalMeanRows 1083).J/2-(generalMeanRows 1083).error (generalMeanGrid j.val)+
      (generalMeanRows 1083).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1083).c)).2-
      (generalMeanRows 1083).J/2-(generalMeanRows 1083).error 4 := by
  have he : (generalMeanRows 1083).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1083) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1083)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1083

/-! Kernel-checked entropy margins for general spectral rectangle 1084. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1084
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6874487922, 6669006191, 6471875095, 6282634335, 6100856244, 5926142900, 5758123560, 5596452363, 5440806266, 5290883200, 5146400393, 5007092863, 4872712056, 4743024603, 4617811192, 4496865543, 4379993470, 4267012025, 4157748711, 4052040763, 3949734487, 3850684653, 3754753930, 3661812376, 3571736957, 3484411103, 3399724308, 3317571744, 3237853912, 3160476321, 3085349179, 3012387117, 2941508922, 2872637299, 2805698637, 2740622802, 2677342938, 2615795278, 2555918977, 2497655944, 2440950696, 2385750212, 2332003800, 2279662976, 2228681342, 2179014480, 2130619845, 2083456673, 2037485885, 1992670001, 1948973064, 1906360560, 1864799346, 1824257584, 1784704678, 1746111212, 1708448894, 1671690502, 1635809836, 1600781665, 1566581687, 1533186485, 1500573483, 1468720914, 1437607778, 1407213811, 1377519452, 1348505812, 1320154643, 1292448314, 1265369782, 1238902569, 1213030736, 1187738862, 1163012022, 1138835768, 1115196109, 1092079492, 1069472784, 1047363260, 1025738579, 1004586776, 983896246, 963655729, 943854295, 924481338, 905526557, 886979951, 868831801, 851072667, 833693375, 816685005, 800038886, 783746585, 767799902, 752190856, 736911684, 721954830, 707312938, 692978848, 678945586, 665206362, 651754562, 638583739, 625687614, 613060068, 600695136, 588587002, 576729997, 565118592, 553747396, 542611149, 531704721, 521023106, 510561421, 500314900, 490278889, 480448849, 470820346, 461389054, 452150745]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1084).prefactor = (5818257943782877/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1084).cutoff/(generalMeanRows 1084).c)).2 =
    (413442320351431/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1084).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1084).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1084).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1084

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1084).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1084).criticalRate j.val*(generalMeanRows 1084).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1084).c*(generalMeanRows 1084).criticalPoint j.val)).2-
      (generalMeanRows 1084).J/2-(generalMeanRows 1084).error (generalMeanGrid j.val)+
      (generalMeanRows 1084).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1084).c)).2-
      (generalMeanRows 1084).J/2-(generalMeanRows 1084).error 4 := by
  have he : (generalMeanRows 1084).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1084) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1084)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1084

/-! Kernel-checked entropy margins for general spectral rectangle 1085. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1085
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7333819304, 7120334494, 6915456410, 6718709568, 6529652285, 6347873688, 6172991053, 6004647422, 5842509468, 5686265571, 5535624093, 5390311807, 5250072486, 5114665614, 4983865223, 4857458821, 4735246424, 4617039670, 4502661002, 4391942920, 4284727303, 4180864772, 4080214110, 3982641732, 3888021182, 3796232685, 3707162718, 3620703620, 3536753229, 3455214547, 3375995421, 3299008257, 3224169748, 3151400619, 3080625393, 3011772174, 2944772436, 2879560838, 2816075041, 2754255543, 2694045519, 2635390677, 2578239120, 2522541217, 2468249481, 2415318455, 2363704610, 2313366236, 2264263358, 2216357640, 2169612302, 2123992048, 2079462985, 2035992554, 1993549470, 1952103654, 1911626177, 1872089205, 1833465947, 1795730605, 1758858328, 1722825167, 1687608038, 1653184675, 1619533600, 1586634084, 1554466113, 1523010360, 1492248152, 1462161442, 1432732785, 1403945308, 1375782688, 1348229129, 1321269342, 1294888519, 1269072320, 1243806847, 1219078634, 1194874623, 1171182152, 1147988938, 1125283064, 1103052962, 1081287404, 1059975484, 1039106611, 1018670495, 998657136, 979056812, 959860075, 941057732, 922640845, 904600717, 886928884, 869617109, 852657373, 836041867, 819762986, 803813325, 788185665, 772872975, 757868400, 743165261, 728757044, 714637397, 700800126, 687239190, 673948695, 660922890, 648156162, 635643035, 623378163, 611356326, 599572427, 588021492, 576698659, 565599182, 554718425, 544051857, 533595052]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1085).prefactor = (3013141965711117/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1085).cutoff/(generalMeanRows 1085).c)).2 =
    (10629316503423/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1085).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1085).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1085).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1085

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1085).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1085).criticalRate j.val*(generalMeanRows 1085).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1085).c*(generalMeanRows 1085).criticalPoint j.val)).2-
      (generalMeanRows 1085).J/2-(generalMeanRows 1085).error (generalMeanGrid j.val)+
      (generalMeanRows 1085).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1085).c)).2-
      (generalMeanRows 1085).J/2-(generalMeanRows 1085).error 4 := by
  have he : (generalMeanRows 1085).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1085) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1085)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1085

/-! Kernel-checked entropy margins for general spectral rectangle 1086. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1086
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7709536751, 7488135642, 7275626205, 7071516577, 6875349904, 6686701255, 6505174850, 6330401600, 6162036887, 5999758577, 5843265226, 5692274456, 5546521490, 5405757821, 5269749997, 5138278521, 5011136845, 4888130443, 4769075977, 4653800517, 4542140834, 4433942745, 4329060515, 4227356298, 4128699626, 4032966938, 3940041139, 3849811198, 3762171764, 3677022828, 3594269387, 3513821151, 3435592258, 3359501014, 3285469648, 3213424085, 3143293735, 3075011294, 3008512559, 2943736252, 2880623863, 2819119493, 2759169716, 2700723441, 2643731790, 2588147981, 2533927214, 2481026572, 2429404920, 2379022815, 2329842418, 2281827417, 2234942945, 2189155512, 2144432936, 2100744280, 2058059787, 2016350831, 1975589856, 1935750329, 1896806692, 1858734312, 1821509448, 1785109198, 1749511471, 1714694945, 1680639035, 1647323859, 1614730208, 1582839517, 1551633835, 1521095803, 1491208625, 1461956045, 1433322327, 1405292232, 1377850995, 1350984311, 1324678314, 1298919556, 1273694999, 1248991989, 1224798250, 1201101864, 1177891257, 1155155192, 1132882749, 1111063319, 1089686589, 1068742534, 1048221404, 1028113715, 1008410243, 989102008, 970180273, 951636531, 933462498, 915650107, 898191498, 881079015, 864305196, 847862768, 831744641, 815943903, 800453811, 785267790, 770379426, 755782460, 741470786, 727438441, 713679610, 700188610, 686959896, 673988053, 661267790, 648793941, 636561458, 624565410, 612800976, 601263449, 589948225]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1086).prefactor = (195054614999299/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1086).cutoff/(generalMeanRows 1086).c)).2 =
    (43108983716501/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1086).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1086).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1086).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1086

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1086).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1086).criticalRate j.val*(generalMeanRows 1086).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1086).c*(generalMeanRows 1086).criticalPoint j.val)).2-
      (generalMeanRows 1086).J/2-(generalMeanRows 1086).error (generalMeanGrid j.val)+
      (generalMeanRows 1086).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1086).c)).2-
      (generalMeanRows 1086).J/2-(generalMeanRows 1086).error 4 := by
  have he : (generalMeanRows 1086).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1086) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1086)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1086

/-! Kernel-checked entropy margins for general spectral rectangle 1087. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1087
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7025929247, 6822565690, 6627167275, 6439312956, 6258610807, 6084695439, 5917225708, 5755882667, 5600367734, 5450401050, 5305720002, 5166077885, 5031242699, 4900996056, 4775132185, 4653457029, 4535787423, 4421950335, 4311782182, 4205128194, 4101841833, 4001784259, 3904823838, 3810835685, 3719701246, 3631307909, 3545548643, 3462321663, 3381530122, 3303081822, 3226888943, 3152867796, 3080938590, 3011025210, 2943055018, 2876958663, 2812669898, 2750125420, 2689264707, 2630029879, 2572365553, 2516218719, 2461538615, 2408276616, 2356386125, 2305822469, 2256542810, 2208506048, 2161672742, 2116005027, 2071466536, 2028022336, 1985638853, 1944283810, 1903926171, 1864536078, 1826084800, 1788544682, 1751889094, 1716092388, 1681129852, 1646977669, 1613612880, 1581013342, 1549157697, 1518025336, 1487596369, 1457851591, 1428772457, 1400341051, 1372540063, 1345352762, 1318762971, 1292755050, 1267313868, 1242424784, 1218073630, 1194246693, 1170930690, 1148112760, 1125780442, 1103921662, 1082524717, 1061578262, 1041071295, 1020993146, 1001333463, 982082201, 963229611, 944766228, 926682863, 908970590, 891620740, 874624888, 857974848, 841662663, 825680598, 810021129, 794676941, 779640918, 764906135, 750465853, 736313516, 722442738, 708847304, 695521160, 682458411, 669653314, 657100272, 644793834, 632728684, 620899643, 609301660, 597929811, 586779293, 575845421, 565123628, 554609455, 544298552, 534186673, 524269676]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1087).prefactor = (2677637476739247/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1087).cutoff/(generalMeanRows 1087).c)).2 =
    (176214326528649/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1087).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1087).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1087).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1087

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1087).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1087).criticalRate j.val*(generalMeanRows 1087).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1087).c*(generalMeanRows 1087).criticalPoint j.val)).2-
      (generalMeanRows 1087).J/2-(generalMeanRows 1087).error (generalMeanGrid j.val)+
      (generalMeanRows 1087).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1087).c)).2-
      (generalMeanRows 1087).J/2-(generalMeanRows 1087).error 4 := by
  have he : (generalMeanRows 1087).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1087) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1087)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1087

/-! Kernel-checked entropy margins for general spectral rectangle 1088. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1088
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6650906070, 6459169355, 6274989246, 6097961777, 5927711093, 5763886960, 5606162557, 5454232499, 5307811068, 5166630627, 5030440187, 4899004120, 4772100991, 4649522501, 4531072521, 4416566223, 4305829273, 4198697109, 4095014267, 3994633766, 3897416552, 3803230971, 3711952297, 3623462287, 3537648778, 3454405306, 3373630759, 3295229051, 3219108826, 3145183172, 3073369368, 3003588637, 2935765919, 2869829668, 2805711647, 2743346750, 2682672824, 2623630517, 2566163118, 2510216422, 2455738594, 2402680047, 2350993321, 2300632981, 2251555503, 2203719186, 2157084056, 2111611781, 2067265589, 2024010191, 1981811710, 1940637612, 1900456642, 1861238763, 1822955096, 1785577871, 1749080370, 1713436880, 1678622650, 1644613841, 1611387492, 1578921475, 1547194459, 1516185877, 1485875890, 1456245357, 1427275804, 1398949394, 1371248902, 1344157688, 1317659674, 1291739317, 1266381589, 1241571958, 1217296363, 1193541199, 1170293296, 1147539903, 1125268670, 1103467636, 1082125208, 1061230150, 1040771571, 1020738908, 1001121916, 981910654, 963095477, 944667021, 926616197, 908934175, 891612382, 874642486, 858016391, 841726229, 825764349, 810123314, 794795887, 779775032, 765053900, 750625828, 736484329, 722623089, 709035957, 695716947, 682660225, 669860108, 657311058, 645007678, 632944710, 621117022, 609519617, 598147616, 586996263, 576060919, 565337056, 554820258, 544506213, 534390713, 524469650, 514739014, 505194889]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1088).prefactor = (1027598602802119/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1088).cutoff/(generalMeanRows 1088).c)).2 =
    (373292110692207/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1088).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1088).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1088).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1088

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1088).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1088).criticalRate j.val*(generalMeanRows 1088).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1088).c*(generalMeanRows 1088).criticalPoint j.val)).2-
      (generalMeanRows 1088).J/2-(generalMeanRows 1088).error (generalMeanGrid j.val)+
      (generalMeanRows 1088).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1088).c)).2-
      (generalMeanRows 1088).J/2-(generalMeanRows 1088).error 4 := by
  have he : (generalMeanRows 1088).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1088) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1088)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1088

/-! Kernel-checked entropy margins for general spectral rectangle 1089. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1089
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6673079538, 6472991610, 6280879792, 6096319019, 5918913689, 5748295063, 5584118944, 5426063612, 5273827973, 5127129902, 4985704736, 4849303935, 4717693852, 4590654629, 4467979191, 4349472325, 4234949847, 4124237834, 4017171929, 3913596692, 3813365013, 3716337571, 3622382328, 3531374073, 3443193988, 3357729260, 3274872713, 3194522463, 3116581612, 3040957948, 2967563676, 2896315161, 2827132694, 2759940271, 2694665384, 2631238831, 2569594533, 2509669369, 2451403012, 2394737785, 2339618521, 2285992430, 2233808978, 2183019773, 2133578452, 2085440583, 2038563565, 1992906541, 1948430310, 1905097245, 1862871222, 1821717541, 1781602865, 1742495151, 1704363590, 1667178551, 1630911527, 1595535082, 1561022801, 1527349249, 1494489920, 1462421203, 1431120336, 1400565374, 1370735149, 1341609241, 1313167940, 1285392223, 1258263719, 1231764683, 1205877973, 1180587021, 1155875811, 1131728858, 1108131184, 1085068299, 1062526181, 1040491258, 1018950389, 997890850, 977300315, 957166839, 937478851, 918225130, 899394801, 880977313, 862962435, 845340240, 828101094, 811235647, 794734821, 778589800, 762792025, 747333179, 732205180, 717400177, 702910537, 688728841, 674847872, 661260615, 647960245, 634940121, 622193784, 609714944, 597497484, 585535443, 573823023, 562354572, 551124590, 540127715, 529358728, 518812539, 508484189, 498368846, 488461799, 478758454, 469254333, 459945068, 450826398, 441894170, 433144329]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1089).prefactor = (673161881210051/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1089).cutoff/(generalMeanRows 1089).c)).2 =
    (177499458822441/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1089).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1089).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1089).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1089

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1089).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1089).criticalRate j.val*(generalMeanRows 1089).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1089).c*(generalMeanRows 1089).criticalPoint j.val)).2-
      (generalMeanRows 1089).J/2-(generalMeanRows 1089).error (generalMeanGrid j.val)+
      (generalMeanRows 1089).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1089).c)).2-
      (generalMeanRows 1089).J/2-(generalMeanRows 1089).error 4 := by
  have he : (generalMeanRows 1089).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1089) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1089)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1089

/-! Kernel-checked entropy margins for general spectral rectangle 1090. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1090
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6467129869, 6278152250, 6096701227, 5922370381, 5754781730, 5593583222, 5438446493, 5289064872, 5145151591, 5006438173, 4872672988, 4743619942, 4619057295, 4498776588, 4382581661, 4270287773, 4161720785, 4056716417, 3955119576, 3856783722, 3761570308, 3669348242, 3579993410, 3493388222, 3409421204, 3327986609, 3248984070, 3172318264, 3097898612, 3025638993, 2955457483, 2887276106, 2821020609, 2756620248, 2694007587, 2633118313, 2573891064, 2516267264, 2460190974, 2405608744, 2352469485, 2300724342, 2250326572, 2201231442, 2153396116, 2106779562, 2061342462, 2017047121, 1973857387, 1931738576, 1890657399, 1850581890, 1811481348, 1773326271, 1736088301, 1699740169, 1664255643, 1629609483, 1595777389, 1562735964, 1530462667, 1498935781, 1468134367, 1438038239, 1408627923, 1379884630, 1351790224, 1324327194, 1297478630, 1271228192, 1245560090, 1220459061, 1195910345, 1171899664, 1148413204, 1125437596, 1102959896, 1080967572, 1059448481, 1038390862, 1017783313, 997614783, 977874556, 958552237, 939637743, 921121288, 902993375, 885244782, 867866556, 850849998, 834186660, 817868329, 801887024, 786234988, 770904675, 755888749, 741180070, 726771696, 712656866, 698829004, 685281706, 672008735, 659004019, 646261643, 633775845, 621541009, 609551663, 597802475, 586288244, 575003900, 563944500, 553105223, 542481365, 532068337, 521861664, 511856974, 502050006, 492436596, 483012682, 473774295, 464717563]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1090).prefactor = (645695299926601/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1090).cutoff/(generalMeanRows 1090).c)).2 =
    (386715131024349/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1090).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1090).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1090).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1090

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1090).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1090).criticalRate j.val*(generalMeanRows 1090).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1090).c*(generalMeanRows 1090).criticalPoint j.val)).2-
      (generalMeanRows 1090).J/2-(generalMeanRows 1090).error (generalMeanGrid j.val)+
      (generalMeanRows 1090).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1090).c)).2-
      (generalMeanRows 1090).J/2-(generalMeanRows 1090).error 4 := by
  have he : (generalMeanRows 1090).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1090) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1090)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1090

/-! Kernel-checked entropy margins for general spectral rectangle 1091. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1091
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6462557555, 6266246096, 6077847105, 5896934553, 5723112105, 5556010497, 5395285210, 5240614379, 5091696934, 4948250920, 4810011988, 4676732029, 4548177944, 4424130520, 4304383414, 4188742226, 4077023651, 3969054710, 3864672036, 3763721225, 3666056242, 3571538868, 3480038194, 3391430157, 3305597103, 3222427390, 3141815018, 3063659286, 2987864474, 2914339543, 2842997867, 2773756969, 2706538286, 2641266946, 2577871561, 2516284028, 2456439354, 2398275479, 2341733122, 2286755629, 2233288834, 2181280928, 2130682335, 2081445596, 2033525261, 1986877785, 1941461436, 1897236196, 1854163685, 1812207073, 1771331007, 1731501542, 1692686068, 1654853248, 1617972960, 1582016237, 1546955215, 1512763080, 1479414021, 1446883185, 1415146632, 1384181294, 1353964939, 1324476128, 1295694187, 1267599171, 1240171829, 1213393580, 1187246481, 1161713200, 1136776993, 1112421676, 1088631604, 1065391649, 1042687177, 1020504032, 998828511, 977647351, 956947710, 936717151, 916943624, 897615453, 878721323, 860250263, 842191635, 824535123, 807270716, 790388703, 773879657, 757734429, 741944133, 726500142, 711394074, 696617788, 682163370, 668023131, 654189595, 640655494, 627413760, 614457518, 601780080, 589374941, 577235767, 565356396, 553730829, 542353225, 531217897, 520319306, 509652058, 499210896, 488990699, 478986479, 469193372, 459606638, 450221656, 441033921, 432039042, 423232733, 414610817, 406169218, 397903962]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1091).prefactor = (5392530305655533/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1091).cutoff/(generalMeanRows 1091).c)).2 =
    (184428756812171/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1091).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1091).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1091).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1091

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1091).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1091).criticalRate j.val*(generalMeanRows 1091).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1091).c*(generalMeanRows 1091).criticalPoint j.val)).2-
      (generalMeanRows 1091).J/2-(generalMeanRows 1091).error (generalMeanGrid j.val)+
      (generalMeanRows 1091).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1091).c)).2-
      (generalMeanRows 1091).J/2-(generalMeanRows 1091).error 4 := by
  have he : (generalMeanRows 1091).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1091) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1091)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1091

/-! Kernel-checked entropy margins for general spectral rectangle 1092. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1092
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6274155029, 6088827813, 5910950551, 5740116710, 5575948400, 5418093852, 5266225156, 5120036254, 4979241126, 4843572172, 4712778745, 4586625835, 4464892867, 4347372622, 4233870242, 4124202339, 4018196170, 3915688889, 3816526859, 3720565021, 3627666317, 3537701157, 3450546930, 3366087546, 3284213024, 3204819103, 3127806886, 3053082503, 2980556811, 2910145103, 2841766844, 2775345424, 2710807927, 2648084919, 2587110245, 2527820845, 2470156577, 2414060055, 2359476497, 2306353582, 2254641315, 2204291904, 2155259639, 2107500785, 2060973477, 2015637623, 1971454809, 1928388219, 1886402550, 1845463936, 1805539879, 1766599176, 1728611861, 1691549141, 1655383341, 1620087848, 1585637065, 1552006359, 1519172016, 1487111201, 1455801916, 1425222960, 1395353896, 1366175016, 1337667305, 1309812416, 1282592636, 1255990860, 1229990566, 1204575788, 1179731094, 1155441561, 1131692758, 1108470722, 1085761940, 1063553331, 1041832226, 1020586357, 999803836, 979473142, 959583105, 940122896, 921082011, 902450259, 884217751, 866374887, 848912349, 831821085, 815092306, 798717469, 782688275, 766996657, 751634771, 736594991, 721869898, 707452277, 693335107, 679511553, 665974967, 652718872, 639736964, 627023102, 614571306, 602375749, 590430754, 578730786, 567270453, 556044499, 545047796, 534275347, 523722276, 513383828, 503255365, 493332360, 483610398, 474085168, 464752464, 455608177, 446648301, 437868919, 429266209]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1092).prefactor = (5170331226466067/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1092).cutoff/(generalMeanRows 1092).c)).2 =
    (80439171374911/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1092).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1092).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1092).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1092

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1092).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1092).criticalRate j.val*(generalMeanRows 1092).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1092).c*(generalMeanRows 1092).criticalPoint j.val)).2-
      (generalMeanRows 1092).J/2-(generalMeanRows 1092).error (generalMeanGrid j.val)+
      (generalMeanRows 1092).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1092).c)).2-
      (generalMeanRows 1092).J/2-(generalMeanRows 1092).error 4 := by
  have he : (generalMeanRows 1092).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1092) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1092)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1092

/-! Kernel-checked entropy margins for general spectral rectangle 1093. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1093
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6339384883, 6147245595, 5962893586, 5785904719, 5615884664, 5452466265, 5295307199, 5144087884, 4998509596, 4858292786, 4723175561, 4592912305, 4467272440, 4346039298, 4229009091, 4115989982, 4006801226, 3901272396, 3799242664, 3700560147, 3605081308, 3512670399, 3423198950, 3336545301, 3252594166, 3171236230, 3092367780, 3015890355, 2941710429, 2869739114, 2799891880, 2732088303, 2666251823, 2602309517, 2540191897, 2479832712, 2421168767, 2364139751, 2308688083, 2254758757, 2202299208, 2151259177, 2101590592, 2053247449, 2006185706, 1960363184, 1915739466, 1872275810, 1829935065, 1788681592, 1748481184, 1709301002, 1671109504, 1633876383, 1597572509, 1562169870, 1527641523, 1493961541, 1461104964, 1429047760, 1397766777, 1367239709, 1337445048, 1308362061, 1279970744, 1252251799, 1225186595, 1198757149, 1172946087, 1147736627, 1123112549, 1099058175, 1075558343, 1052598387, 1030164118, 1008241804, 986818151, 965880285, 945415736, 925412425, 905858644, 886743044, 868054621, 849782705, 831916943, 814447291, 797364001, 780657611, 764318931, 748339041, 732709272, 717421203, 702466653, 687837667, 673526514, 659525675, 645827840, 632425896, 619312925, 606482194, 593927152, 581641420, 569618792, 557853220, 546338818, 535069853, 524040737, 513246029, 502680427, 492338761, 482215996, 472307219, 462607645, 453112606, 443817548, 434718032, 425809727, 417088409, 408549956, 400190346, 392005653]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1093).prefactor = (5378886383274843/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1093).cutoff/(generalMeanRows 1093).c)).2 =
    (390533917126711/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1093).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1093).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1093).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1093

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1093).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1093).criticalRate j.val*(generalMeanRows 1093).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1093).c*(generalMeanRows 1093).criticalPoint j.val)).2-
      (generalMeanRows 1093).J/2-(generalMeanRows 1093).error (generalMeanGrid j.val)+
      (generalMeanRows 1093).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1093).c)).2-
      (generalMeanRows 1093).J/2-(generalMeanRows 1093).error 4 := by
  have he : (generalMeanRows 1093).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1093) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1093)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1093

/-! Kernel-checked entropy margins for general spectral rectangle 1094. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1094
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6047702388, 5850580831, 5661662764, 5480502740, 5306686370, 5139827587, 4979566223, 4825565826, 4677511717, 4535109238, 4398082170, 4266171306, 4139133163, 4016738806, 3898772784, 3785032156, 3675325605, 3569472629, 3467302794, 3368655054, 3273377126, 3181324910, 3092361961, 3006358996, 2923193441, 2842749014, 2764915334, 2689587564, 2616666072, 2546056127, 2477667605, 2411414722, 2347215783, 2284992951, 2224672025, 2166182239, 2109456071, 2054429064, 2001039661, 1949229048, 1898941006, 1850121777, 1802719932, 1756686252, 1711973611, 1668536874, 1626332791, 1585319909, 1545458473, 1506710351, 1469038950, 1432409143, 1396787198, 1362140709, 1328438537, 1295650748, 1263748558, 1232704279, 1202491268, 1173083881, 1144457426, 1116588125, 1089453065, 1063030167, 1037298148, 1012236483, 987825376, 964045728, 940879106, 918307716, 896314378, 874882495, 853996035, 833639507, 813797933, 794456837, 775602217, 757220528, 739298669, 721823959, 704784123, 688167278, 671961917, 656156894, 640741411, 625705006, 611037538, 596729179, 582770397, 569151951, 555864879, 542900484, 530250330, 517906229, 505860236, 494104637, 482631941, 471434876, 460506380, 449839589, 439427840, 429264654, 419343738, 409658975, 400204417, 390974284, 381962954, 373164962, 364574991, 356187869, 347998567, 340002190, 332193976, 324569290, 317123622, 309852583, 302751898, 295817408, 289045060, 282430912, 275971121]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1094).prefactor = (2797927004761251/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1094).cutoff/(generalMeanRows 1094).c)).2 =
    (5567852380913/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1094).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1094).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1094).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1094

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1094).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1094).criticalRate j.val*(generalMeanRows 1094).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1094).c*(generalMeanRows 1094).criticalPoint j.val)).2-
      (generalMeanRows 1094).J/2-(generalMeanRows 1094).error (generalMeanGrid j.val)+
      (generalMeanRows 1094).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1094).c)).2-
      (generalMeanRows 1094).J/2-(generalMeanRows 1094).error 4 := by
  have he : (generalMeanRows 1094).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1094) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1094)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1094

/-! Kernel-checked entropy margins for general spectral rectangle 1095. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1095
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6121980359, 5934991373, 5755642176, 5583512092, 5418210256, 5259372979, 5106661403, 4959759402, 4818371698, 4682222167, 4551052317, 4424619904, 4302697690, 4185072303, 4071543213, 3961921787, 3856030439, 3753701841, 3654778210, 3559110649, 3466558540, 3376988993, 3290276331, 3206301620, 3124952232, 3046121441, 2969708054, 2895616063, 2823754324, 2754036264, 2686379600, 2620706085, 2556941269, 2495014276, 2434857596, 2376406893, 2319600824, 2264380867, 2210691169, 2158478393, 2107691584, 2058282037, 2010203176, 1963410441, 1917861183, 1873514558, 1830331441, 1788274329, 1747307267, 1707395761, 1668506710, 1630608336, 1593670116, 1557662723, 1522557967, 1488328741, 1454948968, 1422393552, 1390638336, 1359660052, 1329436285, 1299945432, 1271166665, 1243079897, 1215665748, 1188905515, 1162781141, 1137275189, 1112370812, 1088051730, 1064302208, 1041107029, 1018451475, 996321305, 974702739, 953582432, 932947467, 912785328, 893083891, 873831404, 855016476, 836628063, 818655451, 801088249, 783916372, 767130033, 750719732, 734676242, 718990603, 703654112, 688658310, 673994980, 659656133, 645634003, 631921036, 618509889, 605393416, 592564666, 580016876, 567743462, 555738017, 543994301, 532506241, 521267921, 510273578, 499517600, 488994518, 478699004, 468625864, 458770038, 449126591, 439690713, 430457714, 421423021, 412582174, 403930821, 395464720, 387179730, 379071812, 371137025, 363371522]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1095).prefactor = (5346509833599933/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1095).cutoff/(generalMeanRows 1095).c)).2 =
    (408432271745029/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1095).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1095).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1095).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1095

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1095).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1095).criticalRate j.val*(generalMeanRows 1095).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1095).c*(generalMeanRows 1095).criticalPoint j.val)).2-
      (generalMeanRows 1095).J/2-(generalMeanRows 1095).error (generalMeanGrid j.val)+
      (generalMeanRows 1095).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1095).c)).2-
      (generalMeanRows 1095).J/2-(generalMeanRows 1095).error 4 := by
  have he : (generalMeanRows 1095).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1095) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1095)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1095

/-! Kernel-checked entropy margins for general spectral rectangle 1096. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1096
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6079018975, 5886373410, 5701704434, 5524573644, 5354573572, 5191324961, 5034474335, 4883691823, 4738669208, 4599118173, 4464768723, 4335367753, 4210677755, 4090475646, 3974551694, 3862708554, 3754760372, 3650531976, 3549858134, 3452582868, 3358558830, 3267646725, 3179714780, 3094638255, 3012298988, 2932584981, 2855390008, 2780613261, 2708159017, 2637936326, 2569858726, 2503843977, 2439813813, 2377693708, 2317412662, 2258903000, 2202100184, 2146942634, 2093371571, 2041330854, 1990766844, 1941628265, 1893866079, 1847433365, 1802285213, 1758378613, 1715672361, 1674126965, 1633704559, 1594368820, 1556084895, 1518819320, 1482539961, 1447215945, 1412817599, 1379316392, 1346684885, 1314896676, 1283926353, 1253749446, 1224342388, 1195682472, 1167747811, 1140517303, 1113970596, 1088088054, 1062850728, 1038240324, 1014239177, 990830223, 967996974, 945723493, 923994376, 902794721, 882110118, 861926621, 842230734, 823009391, 804249942, 785940132, 768068090, 750622312, 733591648, 716965290, 700732755, 684883877, 669408794, 654297937, 639542020, 625132026, 611059204, 597315055, 583891325, 570779995, 557973273, 545463590, 533243587, 521306110, 509644206, 498251113, 487120252, 476245229, 465619818, 455237965, 445093778, 435181522, 425495616, 416030625, 406781259, 397742366, 388908931, 380276066, 371839012, 363593133, 355533911, 347656944, 339957944, 332432730, 325077227, 317887465, 310859570]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1096).prefactor = (2772682599691677/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1096).cutoff/(generalMeanRows 1096).c)).2 =
    (391577940190047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1096).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1096).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1096).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1096

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1096).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1096).criticalRate j.val*(generalMeanRows 1096).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1096).c*(generalMeanRows 1096).criticalPoint j.val)).2-
      (generalMeanRows 1096).J/2-(generalMeanRows 1096).error (generalMeanGrid j.val)+
      (generalMeanRows 1096).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1096).c)).2-
      (generalMeanRows 1096).J/2-(generalMeanRows 1096).error 4 := by
  have he : (generalMeanRows 1096).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1096) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1096)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1096

/-! Kernel-checked entropy margins for general spectral rectangle 1097. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1097
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6397105799, 6196818520, 6004786873, 5820556884, 5643706659, 5473843556, 5310601660, 5153639529, 5002638168, 4857299211, 4717343280, 4582508502, 4452549169, 4327234518, 4206347621, 4089684383, 3977052612, 3868271182, 3763169261, 3661585602, 3563367893, 3468372161, 3376462220, 3287509165, 3201390900, 3117991706, 3037201840, 2958917165, 2883038800, 2809472808, 2738129890, 2668925116, 2601777661, 2536610570, 2473350535, 2411927681, 2352275377, 2294330050, 2238031017, 2183320325, 2130142604, 2078444923, 2028176663, 1979289393, 1931736754, 1885474352, 1840459656, 1796651902, 1754012002, 1712502463, 1672087304, 1632731983, 1594403324, 1557069453, 1520699735, 1485264711, 1450736048, 1417086481, 1384289765, 1352320629, 1321154729, 1290768608, 1261139653, 1232246062, 1204066802, 1176581582, 1149770813, 1123615586, 1098097634, 1073199313, 1048903570, 1025193922, 1002054428, 979469673, 957424740, 935905195, 914897065, 894386819, 874361355, 854807978, 835714387, 817068660, 798859239, 781074915, 763704817, 746738401, 730165432, 713975980, 698160402, 682709339, 667613699, 652864652, 638453621, 624372269, 610612496, 597166427, 584026407, 571184991, 558634940, 546369213, 534380959, 522663512, 511210387, 500015270, 489072016, 478374643, 467917326, 457694392, 447700317, 437929720, 428377358, 419038125, 409907044, 400979264, 392250060, 383714825, 375369066, 367208407, 359228578, 351425416, 343794861]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1097).prefactor = (5751616690439443/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1097).cutoff/(generalMeanRows 1097).c)).2 =
    (397164546898687/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1097).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1097).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1097).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1097

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1097).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1097).criticalRate j.val*(generalMeanRows 1097).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1097).c*(generalMeanRows 1097).criticalPoint j.val)).2-
      (generalMeanRows 1097).J/2-(generalMeanRows 1097).error (generalMeanGrid j.val)+
      (generalMeanRows 1097).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1097).c)).2-
      (generalMeanRows 1097).J/2-(generalMeanRows 1097).error 4 := by
  have he : (generalMeanRows 1097).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1097) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1097)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1097

/-! Kernel-checked entropy margins for general spectral rectangle 1098. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1098
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6732082182, 6523879633, 6324220886, 6132635830, 5948687621, 5771969744, 5602103400, 5438735158, 5281534861, 5130193735, 4984422689, 4843950776, 4708523799, 4577903049, 4451864158, 4330196045, 4212699969, 4099188647, 3989485461, 3883423720, 3780845985, 3681603453, 3585555383, 3492568571, 3402516862, 3315280701, 3230746720, 3148807346, 3069360452, 2992309017, 2917560826, 2845028175, 2774627612, 2706279682, 2639908702, 2575442536, 2512812404, 2451952684, 2392800741, 2335296762, 2279383597, 2225006622, 2172113596, 2120654539, 2070581610, 2021848996, 1974412807, 1928230976, 1883263169, 1839470693, 1796816415, 1755264690, 1714781278, 1675333284, 1636889088, 1599418285, 1562891629, 1527280975, 1492559230, 1458700302, 1425679056, 1393471272, 1362053597, 1331403514, 1301499299, 1272319989, 1243845348, 1216055835, 1188932577, 1162457334, 1136612481, 1111380975, 1086746335, 1062692616, 1039204390, 1016266725, 993865161, 971985696, 950614767, 929739230, 909346347, 889423770, 869959524, 850941995, 832359917, 814202356, 796458701, 779118652, 762172206, 745609650, 729421547, 713598731, 698132292, 683013572, 668234154, 653785852, 639660708, 625850981, 612349139, 599147856, 586240001, 573618635, 561277003, 549208527, 537406803, 525865597, 514578832, 503540594, 492745117, 482186785, 471860124, 461759800, 451880614, 442217498, 432765509, 423519830, 414475763, 405628724, 396974246, 388507969, 380225639]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1098).prefactor = (37284621215547/6250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1098).cutoff/(generalMeanRows 1098).c)).2 =
    (40278253920291/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1098).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1098).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1098).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1098

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1098).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1098).criticalRate j.val*(generalMeanRows 1098).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1098).c*(generalMeanRows 1098).criticalPoint j.val)).2-
      (generalMeanRows 1098).J/2-(generalMeanRows 1098).error (generalMeanGrid j.val)+
      (generalMeanRows 1098).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1098).c)).2-
      (generalMeanRows 1098).J/2-(generalMeanRows 1098).error 4 := by
  have he : (generalMeanRows 1098).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1098) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1098)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1098

/-! Kernel-checked entropy margins for general spectral rectangle 1099. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1099
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7189002746, 6972182938, 6764183746, 6564519065, 6372737286, 6188418245, 6011170511, 5840628948, 5676452541, 5518322433, 5365940160, 5219026055, 5077317799, 4940569114, 4808548567, 4681038485, 4557833963, 4438741958, 4323580458, 4212177719, 4104371569, 4000008766, 3898944399, 3801041348, 3706169779, 3614206675, 3525035408, 3438545337, 3354631440, 3273193967, 3194138125, 3117373777, 3042815167, 2970380666, 2899992525, 2831576657, 2765062429, 2700382460, 2637472446, 2576270985, 2516719420, 2458761686, 2402344174, 2347415597, 2293926867, 2241830979, 2191082904, 2141639485, 2093459343, 2046502785, 2000731717, 1956109570, 1912601220, 1870172916, 1828792217, 1788427927, 1749050035, 1710629658, 1673138991, 1636551252, 1600840640, 1565982285, 1531952211, 1498727289, 1466285205, 1434604422, 1403664144, 1373444288, 1343925449, 1315088871, 1286916425, 1259390576, 1232494361, 1206211366, 1180525704, 1155421992, 1130885330, 1106901284, 1083455868, 1060535522, 1038127103, 1016217862, 994795430, 973847809, 953363353, 933330755, 913739038, 894577539, 875835902, 857504062, 839572238, 822030925, 804870877, 788083107, 771658872, 755589667, 739867216, 724483465, 709430576, 694700918, 680287061, 666181768, 652377991, 638868866, 625647703, 612707984, 600043358, 587647632, 575514771, 563638889, 552014249, 540635255, 529496447, 518592504, 507918229, 497468555, 487238538, 477223351, 467418284, 457818740, 448420230]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1099).prefactor = (154685465767989/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1099).cutoff/(generalMeanRows 1099).c)).2 =
    (414114105212461/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1099).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1099).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1099).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1099

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1099).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1099).criticalRate j.val*(generalMeanRows 1099).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1099).c*(generalMeanRows 1099).criticalPoint j.val)).2-
      (generalMeanRows 1099).J/2-(generalMeanRows 1099).error (generalMeanGrid j.val)+
      (generalMeanRows 1099).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1099).c)).2-
      (generalMeanRows 1099).J/2-(generalMeanRows 1099).error 4 := by
  have he : (generalMeanRows 1099).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1099) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1099)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1099

/-! Kernel-checked entropy margins for general spectral rectangle 1100. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1100
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7566267198, 7340980806, 7124820965, 6917284230, 6717902934, 6526242021, 6341896232, 6164487576, 5993663071, 5829092710, 5670467629, 5517498447, 5369913771, 5227458829, 5089894239, 4956994876, 4828548847, 4704356550, 4584229809, 4467991090, 4355472770, 4246516473, 4140972458, 4038699046, 3939562102, 3843434551, 3750195930, 3659731973, 3571934228, 3486699700, 3403930521, 3323533641, 3245420542, 3169506971, 3095712691, 3023961250, 2954179763, 2886298713, 2820251758, 2755975557, 2693409603, 2632496069, 2573179664, 2515407492, 2459128933, 2404295513, 2350860800, 2298780292, 2248011323, 2198512966, 2150245945, 2103172555, 2057256581, 2012463225, 1968759039, 1926111858, 1884490739, 1843865900, 1804208670, 1765491433, 1727687582, 1690771471, 1654718370, 1619504425, 1585106622, 1551502741, 1518671331, 1486591670, 1455243735, 1424608173, 1394666272, 1365399932, 1336791643, 1308824460, 1281481976, 1254748304, 1228608056, 1203046319, 1178048643, 1153601017, 1129689853, 1106301973, 1083424589, 1061045292, 1039152036, 1017733123, 996777193, 976273211, 956210454, 936578503, 917367226, 898566774, 880167570, 862160296, 844535890, 827285530, 810400634, 793872845, 777694029, 761856264, 746351833, 731173221, 716313107, 701764354, 687520010, 673573297, 659917607, 646546498, 633453687, 620633049, 608078607, 595784532, 583745135, 571954866, 560408310, 549100180, 538025317, 527178683, 516555360, 506150547, 495959554]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1100).prefactor = (1604387582586083/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1100).cutoff/(generalMeanRows 1100).c)).2 =
    (4198284064759/10000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1100).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1100).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1100).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1100

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1100).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1100).criticalRate j.val*(generalMeanRows 1100).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1100).c*(generalMeanRows 1100).criticalPoint j.val)).2-
      (generalMeanRows 1100).J/2-(generalMeanRows 1100).error (generalMeanGrid j.val)+
      (generalMeanRows 1100).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1100).c)).2-
      (generalMeanRows 1100).J/2-(generalMeanRows 1100).error 4 := by
  have he : (generalMeanRows 1100).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1100) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1100)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1100

/-! Kernel-checked entropy margins for general spectral rectangle 1101. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1101
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8294888599, 8063972284, 7842229672, 7629151427, 7424264675, 7227129768, 7037337402, 6854506041, 6678279605, 6508325393, 6344332211, 6186008678, 6033081699, 5885295068, 5742408212, 5604195034, 5470442866, 5340951510, 5215532353, 5094007570, 4976209376, 4861979351, 4751167809, 4643633223, 4539241694, 4437866452, 4339387405, 4243690718, 4150668416, 4060218027, 3972242241, 3886648601, 3803349206, 3722260444, 3643302736, 3566400303, 3491480947, 3418475839, 3347319336, 3277948796, 3210304411, 3144329052, 3079968119, 3017169406, 2955882969, 2896061007, 2837657748, 2780629342, 2724933757, 2670530690, 2617381478, 2565449009, 2514697650, 2465093167, 2416602661, 2369194500, 2322838253, 2277504640, 2233165471, 2189793592, 2147362844, 2105848009, 2065224769, 2025469665, 1986560059, 1948474093, 1911190656, 1874689352, 1838950468, 1803954943, 1769684341, 1736120822, 1703247120, 1671046516, 1639502819, 1608600338, 1578323867, 1548658664, 1519590429, 1491105293, 1463189795, 1435830868, 1409015824, 1382732342, 1356968448, 1331712508, 1306953213, 1282679566, 1258880871, 1235546725, 1212667004, 1190231854, 1168231682, 1146657148, 1125499154, 1104748838, 1084397564, 1064436917, 1044858692, 1025654890, 1006817713, 988339553, 970212987, 952430775, 934985851, 917871317, 901080440, 884606647, 868443517, 852584782, 837024317, 821756139, 806774401, 792073391, 777647526, 763491347, 749599518, 735966824, 722588162, 709458544, 696573091]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1101).prefactor = (3267903165494549/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1101).cutoff/(generalMeanRows 1101).c)).2 =
    (448900221297877/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1101).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1101).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1101).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1101

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1101).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1101).criticalRate j.val*(generalMeanRows 1101).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1101).c*(generalMeanRows 1101).criticalPoint j.val)).2-
      (generalMeanRows 1101).J/2-(generalMeanRows 1101).error (generalMeanGrid j.val)+
      (generalMeanRows 1101).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1101).c)).2-
      (generalMeanRows 1101).J/2-(generalMeanRows 1101).error 4 := by
  have he : (generalMeanRows 1101).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1101) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1101)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1101

/-! Kernel-checked entropy margins for general spectral rectangle 1102. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1102
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6829784740, 6630247023, 6438590992, 6254395721, 6077269565, 5906847574, 5742789186, 5584776170, 5432510783, 5285714118, 5144124612, 5007496703, 4875599615, 4748216250, 4625142195, 4506184801, 4391162354, 4279903315, 4172245621, 4068036045, 3967129614, 3869389061, 3774684334, 3682892132, 3593895485, 3507583355, 3423850278, 3342596026, 3263725289, 3187147391, 3112776013, 3040528945, 2970327849, 2902098041, 2835768285, 2771270603, 2708540094, 2647514770, 2588135394, 2530345339, 2474090445, 2419318891, 2365981077, 2314029503, 2263418667, 2214104962, 2166046579, 2119203421, 2073537015, 2029010436, 1985588228, 1943236334, 1901922030, 1861613864, 1822281589, 1783896114, 1746429447, 1709854643, 1674145760, 1639277809, 1605226714, 1571969273, 1539483112, 1507746657, 1476739094, 1446440337, 1416830996, 1387892350, 1359606314, 1331955419, 1304922777, 1278492067, 1252647502, 1227373815, 1202656234, 1178480460, 1154832655, 1131699417, 1109067764, 1086925122, 1065259304, 1044058497, 1023311249, 1003006452, 983133334, 963681439, 944640625, 926001044, 907753135, 889887614, 872395461, 855267915, 838496461, 822072823, 805988957, 790237038, 774809460, 759698821, 744897921, 730399754, 716197501, 702284522, 688654356, 675300707, 662217447, 649398604, 636838360, 624531046, 612471137, 600653248, 589072128, 577722657, 566599845, 555698822, 545014838, 534543260, 524279567, 514219347, 504358294, 494692206, 485216979]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1102).prefactor = (5385254660623949/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1102).cutoff/(generalMeanRows 1102).c)).2 =
    (92477003176991/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1102).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1102).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1102).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1102

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1102).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1102).criticalRate j.val*(generalMeanRows 1102).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1102).c*(generalMeanRows 1102).criticalPoint j.val)).2-
      (generalMeanRows 1102).J/2-(generalMeanRows 1102).error (generalMeanGrid j.val)+
      (generalMeanRows 1102).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1102).c)).2-
      (generalMeanRows 1102).J/2-(generalMeanRows 1102).error 4 := by
  have he : (generalMeanRows 1102).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1102) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1102)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1102

/-! Kernel-checked entropy margins for general spectral rectangle 1103. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1103
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6479202887, 6292666014, 6113515531, 5941351853, 5775803447, 5616524345, 5463191941, 5315505015, 5173181964, 5035959215, 4903589796, 4775842039, 4652498418, 4533354482, 4418217895, 4306907556, 4199252801, 4095092665, 3994275217, 3896656944, 3802102183, 3710482602, 3621676725, 3535569484, 3452051815, 3371020282, 3292376722, 3216027926, 3141885335, 3069864764, 2999886140, 2931873261, 2865753569, 2801457946, 2738920510, 2678078439, 2618871797, 2561243371, 2505138531, 2450505077, 2397293119, 2345454948, 2294944919, 2245719350, 2197736410, 2150956030, 2105339814, 2060850947, 2017454121, 1975115459, 1933802442, 1893483845, 1854129671, 1815711094, 1778200400, 1741570937, 1705797064, 1670854103, 1636718292, 1603366749, 1570777424, 1538929067, 1507801189, 1477374029, 1447628522, 1418546266, 1390109498, 1362301059, 1335104376, 1308503431, 1282482739, 1257027327, 1232122714, 1207754885, 1183910277, 1160575760, 1137738616, 1115386529, 1093507560, 1072090143, 1051123059, 1030595433, 1010496713, 990816661, 971545344, 952673115, 934190609, 916088731, 898358644, 880991763, 863979741, 847314468, 830988054, 814992829, 799321329, 783966294, 768920657, 754177541, 739730250, 725572263, 711697231, 698098968, 684771448, 671708798, 658905294, 646355357, 634053549, 621994564, 610173231, 598584504, 587223460, 576085298, 565165329, 554458982, 543961789, 533669394, 523577540, 513682072, 503978930, 494464151, 485133863]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1103).prefactor = (5123675206237897/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1103).cutoff/(generalMeanRows 1103).c)).2 =
    (397188285489327/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1103).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1103).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1103).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1103

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1103).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1103).criticalRate j.val*(generalMeanRows 1103).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1103).c*(generalMeanRows 1103).criticalPoint j.val)).2-
      (generalMeanRows 1103).J/2-(generalMeanRows 1103).error (generalMeanGrid j.val)+
      (generalMeanRows 1103).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1103).c)).2-
      (generalMeanRows 1103).J/2-(generalMeanRows 1103).error 4 := by
  have he : (generalMeanRows 1103).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1103) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1103)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1103

/-! Kernel-checked entropy margins for general spectral rectangle 1104. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1104
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6587260080, 6392564576, 6205638756, 6026063238, 5853447995, 5687429767, 5527669747, 5373851519, 5225679210, 5082875829, 4945181769, 4812353460, 4684162143, 4560392763, 4440842958, 4325322145, 4213650678, 4105659087, 4001187368, 3900084350, 3802207097, 3707420363, 3615596098, 3526612980, 3440355987, 3356716007, 3275589468, 3196878001, 3120488125, 3046330952, 2974321920, 2904380537, 2836430144, 2770397697, 2706213562, 2643811323, 2583127603, 2524101895, 2466676407, 2410795915, 2356407624, 2303461039, 2251907845, 2201701794, 2152798593, 2105155809, 2058732774, 2013490491, 1969391555, 1926400071, 1884481584, 1843603002, 1803732537, 1764839635, 1726894923, 1689870151, 1653738138, 1618472726, 1584048727, 1550441883, 1517628823, 1485587019, 1454294757, 1423731089, 1393875810, 1364709420, 1336213092, 1308368648, 1281158527, 1254565761, 1228573950, 1203167237, 1178330287, 1154048263, 1130306809, 1107092030, 1084390469, 1062189098, 1040475292, 1019236820, 998461825, 978138814, 958256640, 938804491, 919771877, 901148618, 882924834, 865090930, 847637589, 830555763, 813836659, 797471732, 781452680, 765771429, 750420129, 735391146, 720677054, 706270628, 692164836, 678352837, 664827969, 651583746, 638613853, 625912139, 613472612, 601289434, 589356916, 577669516, 566221829, 555008587, 544024655, 533265023, 522724807, 512399242, 502283680, 492373587, 482664536, 473152210, 463832394, 454700972, 445753928]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1104).prefactor = (1072578819339483/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1104).cutoff/(generalMeanRows 1104).c)).2 =
    (192694369279087/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1104).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1104).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1104).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1104

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1104).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1104).criticalRate j.val*(generalMeanRows 1104).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1104).c*(generalMeanRows 1104).criticalPoint j.val)).2-
      (generalMeanRows 1104).J/2-(generalMeanRows 1104).error (generalMeanGrid j.val)+
      (generalMeanRows 1104).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1104).c)).2-
      (generalMeanRows 1104).J/2-(generalMeanRows 1104).error 4 := by
  have he : (generalMeanRows 1104).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1104) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1104)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1104

/-! Kernel-checked entropy margins for general spectral rectangle 1105. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1105
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6415719298, 6213930596, 6020366195, 5834583773, 5656171762, 5484746641, 5319950524, 5161449001, 5008929214, 4862098116, 4720680907, 4584419629, 4453071880, 4326409661, 4204218317, 4086295582, 3972450697, 3862503612, 3756284253, 3653631845, 3554394297, 3458427630, 3365595454, 3275768482, 3188824084, 3104645874, 3023123322, 2944151406, 2867630274, 2793464943, 2721565011, 2651844391, 2584221065, 2518616854, 2454957199, 2393170961, 2333190234, 2274950167, 2218388801, 2163446911, 2110067864, 2058197482, 2007783913, 1958777512, 1911130727, 1864797996, 1819735642, 1775901783, 1733256242, 1691760462, 1651377429, 1612071598, 1573808819, 1536556276, 1500282421, 1464956913, 1430550566, 1397035296, 1364384066, 1332570842, 1301570549, 1271359025, 1241912984, 1213209973, 1185228341, 1157947202, 1131346399, 1105406479, 1080108660, 1055434801, 1031367379, 1007889462, 984984683, 962637221, 940831774, 919553543, 898788210, 878521915, 858741247, 839433218, 820585251, 802185164, 784221152, 766681779, 749555957, 732832936, 716502296, 700553925, 684978018, 669765059, 654905815, 640391322, 626212880, 612362038, 598830592, 585610570, 572694230, 560074047, 547742710, 535693110, 523918339, 512411678, 501166595, 490176736, 479435919, 468938133, 458677527, 448648407, 438845231, 429262607, 419895283, 410738146, 401786218, 393034651, 384478722, 376113830, 367935495, 359939351, 352121141, 344476721, 337002049]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1105).prefactor = (5613281860133697/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1105).cutoff/(generalMeanRows 1105).c)).2 =
    (178242496187913/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1105).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1105).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1105).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1105

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1105).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1105).criticalRate j.val*(generalMeanRows 1105).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1105).c*(generalMeanRows 1105).criticalPoint j.val)).2-
      (generalMeanRows 1105).J/2-(generalMeanRows 1105).error (generalMeanGrid j.val)+
      (generalMeanRows 1105).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1105).c)).2-
      (generalMeanRows 1105).J/2-(generalMeanRows 1105).error 4 := by
  have he : (generalMeanRows 1105).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1105) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1105)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1105

/-! Kernel-checked entropy margins for general spectral rectangle 1106. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1106
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6351417000, 6162038631, 5980284438, 5805738317, 5638013521, 5476750059, 5321612394, 5172287368, 5028482356, 4889923597, 4756354698, 4627535274, 4503239725, 4383256123, 4267385195, 4155439410, 4047242126, 3942626834, 3841436443, 3743522639, 3648745290, 3556971904, 3468077121, 3381942250, 3298454846, 3217508308, 3139001515, 3062838488, 2988928072, 2917183645, 2847522847, 2779867327, 2714142504, 2650277354, 2588204201, 2527858525, 2469178789, 2412106267, 2356584891, 2302561105, 2249983727, 2198803821, 2148974578, 2100451205, 2053190814, 2007152327, 1962296382, 1918585244, 1875982723, 1834454096, 1793966036, 1754486538, 1715984858, 1678431453, 1641797918, 1606056935, 1571182221, 1537148479, 1503931352, 1471507379, 1439853955, 1408949290, 1378772375, 1349302944, 1320521445, 1292409003, 1264947395, 1238119020, 1211906874, 1186294522, 1161266074, 1136806164, 1112899930, 1089532987, 1066691415, 1044361733, 1022530888, 1001186233, 980315514, 959906852, 939948733, 920429989, 901339785, 882667613, 864403271, 846536857, 829058756, 811959632, 795230415, 778862292, 762846698, 747175309, 731840033, 716832998, 702146551, 687773245, 673705836, 659937273, 646460693, 633269417, 620356938, 607716924, 595343204, 583229767, 571370759, 559760472, 548393347, 537263961, 526367031, 515697404, 505250056, 495020086, 485002715, 475193281, 465587234, 456180136, 446967656, 437945566, 429109739, 420456148, 411980860]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1106).prefactor = (5326634503011033/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1106).cutoff/(generalMeanRows 1106).c)).2 =
    (403021288159517/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1106).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1106).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1106).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1106

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1106).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1106).criticalRate j.val*(generalMeanRows 1106).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1106).c*(generalMeanRows 1106).criticalPoint j.val)).2-
      (generalMeanRows 1106).J/2-(generalMeanRows 1106).error (generalMeanGrid j.val)+
      (generalMeanRows 1106).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1106).c)).2-
      (generalMeanRows 1106).J/2-(generalMeanRows 1106).error 4 := by
  have he : (generalMeanRows 1106).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1106) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1106)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1106

/-! Kernel-checked entropy margins for general spectral rectangle 1107. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1107
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6431899795, 6235226165, 6046537852, 5865399771, 5691407443, 5524184298, 5363379262, 5208664610, 5059734034, 4916300910, 4778096736, 4644869720, 4516383501, 4392415990, 4272758319, 4157213873, 4045597420, 3937734310, 3833459733, 3732618057, 3635062199, 3540653064, 3449259017, 3360755399, 3275024086, 3191953066, 3111436068, 3033372202, 2957665627, 2884225257, 2812964464, 2743800824, 2676655868, 2611454852, 2548126546, 2486603031, 2426819515, 2368714162, 2312227922, 2257304385, 2203889635, 2151932116, 2101382508, 2052193610, 2004320225, 1957719061, 1912348630, 1868169158, 1825142498, 1783232048, 1742402674, 1702620640, 1663853538, 1626070222, 1589240753, 1553336334, 1518329263, 1484192878, 1450901510, 1418430435, 1386755835, 1355854754, 1325705058, 1296285404, 1267575199, 1239554570, 1212204332, 1185505959, 1159441556, 1133993832, 1109146072, 1084882119, 1061186345, 1038043631, 1015439349, 993359340, 971789894, 950717736, 930130003, 910014234, 890358354, 871150652, 852379777, 834034717, 816104792, 798579636, 781449189, 764703686, 748333646, 732329860, 716683383, 701385524, 686427839, 671802120, 657500388, 643514884, 629838063, 616462588, 603381320, 590587312, 578073806, 565834222, 553862157, 542151376, 530695807, 519489538, 508526809, 497802010, 487309676, 477044481, 467001232, 457174873, 447560470, 438153217, 428948426, 419941525, 411128058, 402503675, 394064137, 385805305, 377723143]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1107).prefactor = (5552663320647293/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1107).cutoff/(generalMeanRows 1107).c)).2 =
    (391625153428649/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1107).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1107).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1107).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1107

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1107).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1107).criticalRate j.val*(generalMeanRows 1107).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1107).c*(generalMeanRows 1107).criticalPoint j.val)).2-
      (generalMeanRows 1107).J/2-(generalMeanRows 1107).error (generalMeanGrid j.val)+
      (generalMeanRows 1107).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1107).c)).2-
      (generalMeanRows 1107).J/2-(generalMeanRows 1107).error 4 := by
  have he : (generalMeanRows 1107).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1107) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1107)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1107

/-! Kernel-checked entropy margins for general spectral rectangle 1108. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1108
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6167973764, 5984154313, 5807771233, 5638413880, 5475700871, 5319277495, 5168813401, 5024000529, 4884551264, 4750196762, 4620685453, 4495781684, 4375264487, 4258926469, 4146572797, 4038020270, 3933096485, 3831639060, 3733494933, 3638519713, 3546577089, 3457538283, 3371281547, 3287691701, 3206659704, 3128082260, 3051861455, 2977904411, 2906122983, 2836433459, 2768756294, 2703015859, 2639140204, 2577060846, 2516712562, 2458033201, 2400963508, 2345446961, 2291429612, 2238859951, 2187688764, 2137869012, 2089355711, 2042105819, 1996078139, 1951233216, 1907533245, 1864941991, 1823424703, 1782948040, 1743479999, 1704989851, 1667448074, 1630826295, 1595097232, 1560234647, 1526213288, 1493008848, 1460597919, 1428957949, 1398067201, 1367904721, 1338450296, 1309684425, 1281588286, 1254143705, 1227333128, 1201139595, 1175546714, 1150538636, 1126100032, 1102216073, 1078872408, 1056055143, 1033750825, 1011946424, 990629313, 969787255, 949408387, 929481205, 909994550, 890937597, 872299838, 854071076, 836241408, 818801217, 801741161, 785052163, 768725402, 752752303, 737124531, 721833977, 706872756, 692233199, 677907840, 663889415, 650170854, 636745272, 623605968, 610746413, 598160248, 585841280, 573783472, 561980943, 550427961, 539118937, 528048424, 517211109, 506601812, 496215482, 486047189, 476092126, 466345602, 456803041, 447459975, 438312045, 429354995, 420584672, 411997019, 403588077, 395353978]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1108).prefactor = (527644327818319/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1108).cutoff/(generalMeanRows 1108).c)).2 =
    (42572209392871/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1108).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1108).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1108).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1108

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1108).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1108).criticalRate j.val*(generalMeanRows 1108).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1108).c*(generalMeanRows 1108).criticalPoint j.val)).2-
      (generalMeanRows 1108).J/2-(generalMeanRows 1108).error (generalMeanGrid j.val)+
      (generalMeanRows 1108).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1108).c)).2-
      (generalMeanRows 1108).J/2-(generalMeanRows 1108).error 4 := by
  have he : (generalMeanRows 1108).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1108) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1108)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1108

/-! Kernel-checked entropy margins for general spectral rectangle 1109. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1109
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6314912391, 6124311491, 5941454593, 5765914453, 5597294229, 5435224788, 5279362307, 5129386128, 4984996837, 4845914529, 4711877252, 4582639600, 4457971430, 4337656712, 4221492475, 4109287842, 4000863165, 3896049217, 3794686464, 3696624395, 3601720899, 3509841705, 3420859859, 3334655237, 3251114110, 3170128725, 3091596931, 3015421824, 2941511425, 2869778372, 2800139645, 2732516301, 2666833233, 2603018942, 2541005331, 2480727502, 2422123576, 2365134524, 2309704002, 2255778206, 2203305731, 2152237435, 2102526326, 2054127436, 2006997722, 1961095960, 1916382650, 1872819929, 1830371485, 1789002480, 1748679472, 1709370351, 1671044268, 1633671574, 1597223764, 1561673420, 1526994158, 1493160582, 1460148234, 1427933554, 1396493836, 1365807188, 1335852499, 1306609400, 1278058235, 1250180025, 1222956441, 1196369775, 1170402915, 1145039317, 1120262983, 1096058438, 1072410707, 1049305297, 1026728173, 1004665746, 983104849, 962032723, 941437003, 921305698, 901627181, 882390173, 863583730, 845197231, 827220365, 809643122, 792455779, 775648890, 759213280, 743140031, 727420474, 712046182, 697008960, 682300837, 667914061, 653841086, 640074573, 626607377, 613432542, 600543297, 587933046, 575595369, 563524010, 551712873, 540156020, 528847666, 517782169, 506954032, 496357895, 485988534, 475840851, 465909878, 456190767, 446678790, 437369334, 428257899, 419340092, 410611628, 402068325, 393706100, 385520966]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1109).prefactor = (5481224001317099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1109).cutoff/(generalMeanRows 1109).c)).2 =
    (210059919190021/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1109).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1109).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1109).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1109

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1109).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1109).criticalRate j.val*(generalMeanRows 1109).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1109).c*(generalMeanRows 1109).criticalPoint j.val)).2-
      (generalMeanRows 1109).J/2-(generalMeanRows 1109).error (generalMeanGrid j.val)+
      (generalMeanRows 1109).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1109).c)).2-
      (generalMeanRows 1109).J/2-(generalMeanRows 1109).error 4 := by
  have he : (generalMeanRows 1109).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1109) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1109)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1109

/-! Kernel-checked entropy margins for general spectral rectangle 1110. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1110
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6281407741, 6084679373, 5896051614, 5715078467, 5541345535, 5374467227, 5214084272, 5059861493, 4911485811, 4768664449, 4631123313, 4498605535, 4370870141, 4247690858, 4128855014, 4014162547, 3903425095, 3796465167, 3693115381, 3593217767, 3496623127, 3403190446, 3312786350, 3225284604, 3140565652, 3058516192, 2979028776, 2902001450, 2827337411, 2754944694, 2684735880, 2616627824, 2550541401, 2486401271, 2424135662, 2363676161, 2304957527, 2247917508, 2192496679, 2138638284, 2086288087, 2035394241, 1985907154, 1937779373, 1890965469, 1845421931, 1801107070, 1757980920, 1716005154, 1675143000, 1635359165, 1596619759, 1558892227, 1522145286, 1486348860, 1451474026, 1417492956, 1384378867, 1352105973, 1320649438, 1289985333, 1260090594, 1230942983, 1202521053, 1174804112, 1147772187, 1121405999, 1095686927, 1070596985, 1046118790, 1022235540, 998930991, 976189430, 953995657, 932334963, 911193109, 890556308, 870411210, 850744881, 831544787, 812798784, 794495095, 776622303, 759169334, 742125447, 725480217, 709223528, 693345561, 677836783, 662687934, 647890023, 633434313, 619312317, 605515785, 592036701, 578867269, 565999910, 553427255, 541142135, 529137577, 517406796, 505943192, 494740337, 483791980, 473092033, 462634568, 452413815, 442424152, 432660106, 423116345, 413787674, 404669031, 395755486, 387042232, 378524585, 370197980, 362057966, 354100205, 346320465, 338714621, 331278652]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1110).prefactor = (5693952340365049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1110).cutoff/(generalMeanRows 1110).c)).2 =
    (50437369643/125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1110).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1110).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1110).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1110

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1110).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1110).criticalRate j.val*(generalMeanRows 1110).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1110).c*(generalMeanRows 1110).criticalPoint j.val)).2-
      (generalMeanRows 1110).J/2-(generalMeanRows 1110).error (generalMeanGrid j.val)+
      (generalMeanRows 1110).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1110).c)).2-
      (generalMeanRows 1110).J/2-(generalMeanRows 1110).error 4 := by
  have he : (generalMeanRows 1110).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1110) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1110)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1110

/-! Kernel-checked entropy margins for general spectral rectangle 1111. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1111
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6249993024, 6047192584, 5852860081, 5666529805, 5487768907, 5316174501, 5151371084, 4993008224, 4840758491, 4694315591, 4553392687, 4417720883, 4287047847, 4161136563, 4039764199, 3922721070, 3809809695, 3700843938, 3595648212, 3494056757, 3395912976, 3301068820, 3209384225, 3120726591, 3034970305, 2951996292, 2871691608, 2793949059, 2718666846, 2645748238, 2575101271, 2506638458, 2440276534, 2375936201, 2313541908, 2253021632, 2194306681, 2137331506, 2082033529, 2028352977, 1976232734, 1925618193, 1876457125, 1828699552, 1782297631, 1737205540, 1693379377, 1650777060, 1609358237, 1569084197, 1529917789, 1491823348, 1454766619, 1418714689, 1383635925, 1349499912, 1316277395, 1283940226, 1252461309, 1221814559, 1191974849, 1162917969, 1134620586, 1107060205, 1080215131, 1054064435, 1028587919, 1003766088, 979580117, 956011824, 933043646, 910658606, 888840296, 867572852, 846840929, 826629684, 806924754, 787712238, 768978679, 750711045, 732896715, 715523462, 698579439, 682053164, 665933507, 650209676, 634871207, 619907947, 605310051, 591067962, 577172408, 563614387, 550385162, 537476246, 524879401, 512586621, 500590132, 488882380, 477456023, 466303926, 455419154, 444794965, 434424804, 424302296, 414421242, 404775611, 395359537, 386167313, 377193387, 368432354, 359878955, 351528072, 343374721, 335414052, 327641342, 320051991, 312641521, 305405571, 298339892, 291440348, 284702905]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1111).prefactor = (5914936745252171/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1111).cutoff/(generalMeanRows 1111).c)).2 =
    (387149819142471/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1111).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1111).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1111).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1111

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1111).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1111).criticalRate j.val*(generalMeanRows 1111).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1111).c*(generalMeanRows 1111).criticalPoint j.val)).2-
      (generalMeanRows 1111).J/2-(generalMeanRows 1111).error (generalMeanGrid j.val)+
      (generalMeanRows 1111).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1111).c)).2-
      (generalMeanRows 1111).J/2-(generalMeanRows 1111).error 4 := by
  have he : (generalMeanRows 1111).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1111) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1111)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1111

/-! Kernel-checked entropy margins for general spectral rectangle 1112. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1112
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6586259728, 6375020903, 6172560957, 5978396954, 5792080080, 5613192632, 5441345335, 5276174944, 5117342091, 4964529344, 4817439471, 4675793855, 4539331068, 4407805575, 4280986557, 4158656835, 4040611889, 3926658964, 3816616247, 3710312116, 3607584450, 3508279989, 3412253752, 3319368496, 3229494214, 3142507682, 3058292023, 2976736320, 2897735243, 2821188715, 2747001591, 2675083366, 2605347904, 2537713179, 2472101042, 2408436996, 2346649989, 2286672225, 2228438980, 2171888431, 2116961505, 2063601722, 2011755064, 1961369838, 1912396559, 1864787831, 1818498243, 1773484266, 1729704157, 1687117867, 1645686964, 1605374545, 1566145168, 1527964775, 1490800630, 1454621254, 1419396368, 1385096833, 1351694599, 1319162656, 1287474985, 1256606515, 1226533077, 1197231367, 1168678908, 1140854013, 1113735749, 1087303908, 1061538973, 1036422093, 1011935049, 988060233, 964780623, 942079754, 919941701, 898351054, 877292900, 856752800, 836716776, 817171286, 798103212, 779499846, 761348868, 743638335, 726356669, 709492640, 693035355, 676974246, 661299056, 645999833, 631066913, 616490914, 602262726, 588373500, 574814640, 561577793, 548654844, 536037903, 523719305, 511691594, 499947522, 488480041, 477282295, 466347616, 455669516, 445241684, 435057975, 425112414, 415399180, 405912611, 396647190, 387597551, 378758464, 370124837, 361691713, 353454260, 345407773, 337547668, 329869479, 322368854, 315041550]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1112).prefactor = (3072248818479861/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1112).cutoff/(generalMeanRows 1112).c)).2 =
    (392569886611811/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1112).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1112).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1112).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1112

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1112).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1112).criticalRate j.val*(generalMeanRows 1112).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1112).c*(generalMeanRows 1112).criticalPoint j.val)).2-
      (generalMeanRows 1112).J/2-(generalMeanRows 1112).error (generalMeanGrid j.val)+
      (generalMeanRows 1112).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1112).c)).2-
      (generalMeanRows 1112).J/2-(generalMeanRows 1112).error 4 := by
  have he : (generalMeanRows 1112).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1112) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1112)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1112

/-! Kernel-checked entropy margins for general spectral rectangle 1113. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1113
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7041510256, 6820976121, 6609522836, 6406650435, 6211894375, 6024822406, 5845031781, 5672146765, 5505816393, 5345712459, 5191527704, 5042974173, 4899781736, 4761696736, 4628480768, 4499909559, 4375771956, 4255868989, 4140013020, 4028026965, 3919743571, 3815004760, 3713661017, 3615570832, 3520600184, 3428622057, 3339516004, 3253167732, 3169468724, 3088315887, 3009611224, 2933261527, 2859178097, 2787276479, 2717476214, 2649700611, 2583876534, 2519934199, 2457806990, 2397431281, 2338746276, 2281693851, 2226218416, 2172266773, 2119787998, 2068733314, 2019055987, 1970711214, 1923656032, 1877849218, 1833251208, 1789824012, 1747531136, 1706337510, 1666209419, 1627114440, 1589021378, 1551900209, 1515722027, 1480458991, 1446084274, 1412572023, 1379897309, 1348036090, 1316965168, 1286662156, 1257105440, 1228274147, 1200148113, 1172707853, 1145934532, 1119809938, 1094316460, 1069437056, 1045155238, 1021455044, 998321019, 975738197, 953692078, 932168614, 911154188, 890635601, 870600053, 851035130, 831928790, 813269349, 795045466, 777246134, 759860664, 742878679, 726290097, 710085127, 694254252, 678788225, 663678060, 648915017, 634490601, 620396550, 606624829, 593167619, 580017317, 567166520, 554608028, 542334829, 530340099, 518617194, 507159644, 495961149, 485015573, 474316937, 463859419, 453637345, 443645187, 433877557, 424329204, 414995011, 405869988, 396949271, 388228117, 379701904, 371366121]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1113).prefactor = (6382967872126253/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1113).cutoff/(generalMeanRows 1113).c)).2 =
    (50437369643/125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1113).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1113).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1113).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1113

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1113).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1113).criticalRate j.val*(generalMeanRows 1113).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1113).c*(generalMeanRows 1113).criticalPoint j.val)).2-
      (generalMeanRows 1113).J/2-(generalMeanRows 1113).error (generalMeanGrid j.val)+
      (generalMeanRows 1113).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1113).c)).2-
      (generalMeanRows 1113).J/2-(generalMeanRows 1113).error 4 := by
  have he : (generalMeanRows 1113).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1113) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1113)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1113

/-! Kernel-checked entropy margins for general spectral rectangle 1114. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1114
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7529252128, 7299140828, 7078419925, 6866571755, 6663115436, 6467603612, 6279619555, 6098774570, 5924705671, 5757073483, 5595560364, 5439868696, 5289719344, 5144850256, 5005015192, 4869982560, 4739534363, 4613465228, 4491581521, 4373700538, 4259649756, 4149266148, 4042395552, 3938892088, 3838617624, 3741441273, 3647238940, 3555892893, 3467291370, 3381328211, 3297902521, 3216918352, 3138284411, 3061913783, 2987723679, 2915635196, 2845573096, 2777465601, 2711244194, 2646843441, 2584200822, 2523256572, 2463953530, 2406237001, 2350054627, 2295356261, 2242093854, 2190221347, 2139694566, 2090471130, 2042510359, 1995773191, 1950222098, 1905821015, 1862535269, 1820331508, 1779177643, 1739042784, 1699897187, 1661712200, 1624460211, 1588114602, 1552649705, 1518040758, 1484263864, 1451295956, 1419114756, 1387698748, 1357027137, 1327079824, 1297837376, 1269280996, 1241392501, 1214154290, 1187549327, 1161561115, 1136173676, 1111371528, 1087139670, 1063463557, 1040329091, 1017722594, 995630801, 974040839, 952940216, 932316803, 912158826, 892454847, 873193758, 854364766, 835957383, 817961412, 800366945, 783164343, 766344236, 749897506, 733815286, 718088947, 702710089, 687670540, 672962341, 658577745, 644509208, 630749380, 617291105, 604127410, 591251500, 578656756, 566336725, 554285118, 542495804, 530962807, 519680298, 508642595, 497844155, 487279571, 476943571, 466831010, 456936869, 447256250, 437784374]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1114).prefactor = (132613864513601/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1114).cutoff/(generalMeanRows 1114).c)).2 =
    (414548793330587/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1114).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1114).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1114).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1114

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1114).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1114).criticalRate j.val*(generalMeanRows 1114).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1114).c*(generalMeanRows 1114).criticalPoint j.val)).2-
      (generalMeanRows 1114).J/2-(generalMeanRows 1114).error (generalMeanGrid j.val)+
      (generalMeanRows 1114).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1114).c)).2-
      (generalMeanRows 1114).J/2-(generalMeanRows 1114).error 4 := by
  have he : (generalMeanRows 1114).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1114) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1114)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1114

/-! Kernel-checked entropy margins for general spectral rectangle 1115. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1115
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8164854046, 7927754067, 7700166119, 7481563804, 7271458348, 7069395260, 6874951362, 6687732127, 6507369293, 6333518725, 6165858472, 6004087031, 5847921758, 5697097440, 5551364987, 5410490243, 5274252907, 5142445539, 5014872653, 4891349885, 4771703235, 4655768357, 4543389919, 4434421005, 4328722564, 4226162906, 4126617229, 4029967183, 3936100472, 3844910476, 3756295903, 3670160471, 3586412602, 3504965148, 3425735127, 3348643483, 3273614857, 3200577377, 3129462464, 3060204639, 2992741360, 2927012853, 2862961967, 2800534025, 2739676698, 2680339876, 2622475553, 2566037715, 2510982242, 2457266802, 2404850769, 2353695130, 2303762411, 2255016592, 2207423046, 2160948461, 2115560784, 2071229158, 2027923864, 1985616269, 1944278775, 1903884772, 1864408592, 1825825466, 1788111485, 1751243559, 1715199383, 1679957404, 1645496785, 1611797375, 1578839684, 1546604849, 1515074611, 1484231292, 1454057766, 1424537442, 1395654239, 1367392568, 1339737308, 1312673796, 1286187801, 1260265511, 1234893520, 1210058805, 1185748722, 1161950981, 1138653643, 1115845101, 1093514070, 1071649575, 1050240942, 1029277787, 1008750003, 988647755, 968961466, 949681813, 930799717, 912306332, 894193043, 876451454, 859073382, 842050852, 825376087, 809041507, 793039718, 777363508, 762005845, 746959863, 732218867, 717776322, 703625849, 689761221, 676176360, 662865331, 649822338, 637041721, 624517951, 612245629, 600219479, 588434345, 576885193]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1115).prefactor = (1695979936466597/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1115).cutoff/(generalMeanRows 1115).c)).2 =
    (109255412295661/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1115).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1115).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1115).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1115

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1115).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1115).criticalRate j.val*(generalMeanRows 1115).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1115).c*(generalMeanRows 1115).criticalPoint j.val)).2-
      (generalMeanRows 1115).J/2-(generalMeanRows 1115).error (generalMeanGrid j.val)+
      (generalMeanRows 1115).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1115).c)).2-
      (generalMeanRows 1115).J/2-(generalMeanRows 1115).error 4 := by
  have he : (generalMeanRows 1115).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1115) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1115)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1115

/-! Kernel-checked entropy margins for general spectral rectangle 1116. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1116
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5436954367, 5253112993, 5077154273, 4908634909, 4747143447, 4592297457, 4443741012, 4301142432, 4164192261, 4032601445, 3906099692, 3784433984, 3667367234, 3554677072, 3446154725, 3341604018, 3240840447, 3143690338, 3049990077, 2959585405, 2872330768, 2788088727, 2706729403, 2628129977, 2552174227, 2478752094, 2407759288, 2339096920, 2272671163, 2208392938, 2146177619, 2085944764, 2027617864, 1971124106, 1916394157, 1863361961, 1811964547, 1762141857, 1713836578, 1666993989, 1621561817, 1577490105, 1534731082, 1493239048, 1452970265, 1413882847, 1375936674, 1339093289, 1303315823, 1268568905, 1234818596, 1202032310, 1170178754, 1139227858, 1109150722, 1079919556, 1051507632, 1023889227, 997039584, 970934862, 945552097, 920869163, 896864731, 873518237, 850809849, 828720431, 807231518, 786325284, 765984517, 746192591, 726933445, 708191557, 689951924, 672200039, 654921872, 638103855, 621732855, 605796168, 590281493, 575176922, 560470923, 546152328, 532210317, 518634406, 505414435, 492540557, 480003224, 467793180, 455901447, 444319320, 433038350, 422050344, 411347348, 400921647, 390765748, 380872380, 371234482, 361845200, 352697876, 343786043, 335103421, 326643907, 318401575, 310370663, 302545575, 294920869, 287491259, 280251604, 273196908, 266322314, 259623098, 253094667, 246732555, 240532420, 234490035, 228601291, 222862193, 217268851, 211817481, 206504404, 201326038]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1116).prefactor = (5662550296695723/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1116).cutoff/(generalMeanRows 1116).c)).2 =
    (208907495558603/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1116).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1116).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1116).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1116

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1116).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1116).criticalRate j.val*(generalMeanRows 1116).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1116).c*(generalMeanRows 1116).criticalPoint j.val)).2-
      (generalMeanRows 1116).J/2-(generalMeanRows 1116).error (generalMeanGrid j.val)+
      (generalMeanRows 1116).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1116).c)).2-
      (generalMeanRows 1116).J/2-(generalMeanRows 1116).error 4 := by
  have he : (generalMeanRows 1116).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1116) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1116)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1116

/-! Kernel-checked entropy margins for general spectral rectangle 1117. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1117
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6621885931, 6436870838, 6259111830, 6088214719, 5923813141, 5765566085, 5613155700, 5466285333, 5324677774, 5188073672, 5056230120, 4928919364, 4805927647, 4687054152, 4572110042, 4460917594, 4353309396, 4249127623, 4148223372, 4050456048, 3955692804, 3863808025, 3774682854, 3688204751, 3604267090, 3522768784, 3443613937, 3366711527, 3291975101, 3219322507, 3148675629, 3079960153, 3013105341, 2948043825, 2884711414, 2823046910, 2762991943, 2704490811, 2647490332, 2591939705, 2537790385, 2484995955, 2433512018, 2383296083, 2334307475, 2286507230, 2239858013, 2194324033, 2149870962, 2106465867, 2064077132, 2022674402, 1982228513, 1942711438, 1904096231, 1866356976, 1829468735, 1793407506, 1758150176, 1723674479, 1689958961, 1656982937, 1624726463, 1593170296, 1562295866, 1532085247, 1502521126, 1473586778, 1445266040, 1417543288, 1390403413, 1363831797, 1337814297, 1312337224, 1287387321, 1262951748, 1239018067, 1215574222, 1192608526, 1170109645, 1148066588, 1126468686, 1105305590, 1084567250, 1064243907, 1044326083, 1024804570, 1005670418, 986914929, 968529646, 950506343, 932837019, 915513892, 898529385, 881876124, 865546932, 849534815, 833832966, 818434751, 803333707, 788523533, 773998090, 759751392, 745777599, 732071021, 718626101, 705437423, 692499699, 679807770, 667356597, 655141266, 643156973, 631399032, 619862863, 608543993, 597438052, 586540770, 575847976, 565355591, 555059629, 544956195]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1117).prefactor = (5106378666183709/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1117).cutoff/(generalMeanRows 1117).c)).2 =
    (83112760206057/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1117).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1117).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1117).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1117

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1117).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1117).criticalRate j.val*(generalMeanRows 1117).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1117).c*(generalMeanRows 1117).criticalPoint j.val)).2-
      (generalMeanRows 1117).J/2-(generalMeanRows 1117).error (generalMeanGrid j.val)+
      (generalMeanRows 1117).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1117).c)).2-
      (generalMeanRows 1117).J/2-(generalMeanRows 1117).error 4 := by
  have he : (generalMeanRows 1117).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1117) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1117)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1117

/-! Kernel-checked entropy margins for general spectral rectangle 1118. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1118
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6656918293, 6463315375, 6277392252, 6098733326, 5926952203, 5761689113, 5602608607, 5449397502, 5301763037, 5159431220, 5022145337, 4889664605, 4761762954, 4638227922, 4518859651, 4403469968, 4291881558, 4183927194, 4079449040, 3978298012, 3880333188, 3785421265, 3693436063, 3604258063, 3517773983, 3433876383, 3352463304, 3273437930, 3196708271, 3122186880, 3049790577, 2979440199, 2911060367, 2844579267, 2779928446, 2717042623, 2655859509, 2596319645, 2538366243, 2481945041, 2427004168, 2373494016, 2321367119, 2270578039, 2221083265, 2172841110, 2125811616, 2079956470, 2035238920, 1991623696, 1949076937, 1907566121, 1867060001, 1827528544, 1788942871, 1751275202, 1714498806, 1678587951, 1643517857, 1609264652, 1575805332, 1543117721, 1511180433, 1479972838, 1449475028, 1419667784, 1390532549, 1362051396, 1334207004, 1306982630, 1280362088, 1254329721, 1228870381, 1203969411, 1179612620, 1155786269, 1132477050, 1109672067, 1087358826, 1065525213, 1044159482, 1023250242, 1002786441, 982757354, 963152572, 943961988, 925175788, 906784440, 888778682, 871149513, 853888187, 836986199, 820435279, 804227383, 788354688, 772809580, 757584650, 742672687, 728066670, 713759762, 699745306, 686016815, 672567972, 659392620, 646484759, 633838539, 621448261, 609308364, 597413427, 585758164, 574337416, 563146152, 552179463, 541432557, 530900759, 520579504, 510464337, 500550908, 490834969, 481312371, 471979064]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1118).prefactor = (5362031197730797/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1118).cutoff/(generalMeanRows 1118).c)).2 =
    (24876218211211/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1118).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1118).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1118).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1118

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1118).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1118).criticalRate j.val*(generalMeanRows 1118).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1118).c*(generalMeanRows 1118).criticalPoint j.val)).2-
      (generalMeanRows 1118).J/2-(generalMeanRows 1118).error (generalMeanGrid j.val)+
      (generalMeanRows 1118).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1118).c)).2-
      (generalMeanRows 1118).J/2-(generalMeanRows 1118).error 4 := by
  have he : (generalMeanRows 1118).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1118) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1118)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1118

/-! Kernel-checked entropy margins for general spectral rectangle 1119. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1119
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6694413321, 6492127426, 6297965100, 6111487975, 5932288355, 5759986515, 5594228284, 5434682889, 5281041027, 5133013127, 4990327783, 4852730351, 4719981661, 4591856865, 4468144379, 4348644925, 4233170654, 4121544347, 4013598678, 3909175545, 3808125450, 3710306932, 3615586041, 3523835858, 3434936044, 3348772432, 3265236642, 3184225727, 3105641845, 3029391953, 2955387524, 2883544279, 2813781946, 2746024028, 2680197588, 2616233048, 2554064008, 2493627063, 2434861646, 2377709868, 2322116383, 2268028244, 2215394785, 2164167495, 2114299911, 2065747512, 2018467620, 1972419305, 1927563304, 1883861931, 1841279004, 1799779770, 1759330837, 1719900110, 1681456723, 1643970991, 1607414345, 1571759288, 1536979341, 1503048998, 1469943681, 1437639700, 1406114214, 1375345188, 1345311367, 1315992233, 1287367977, 1259419471, 1232128236, 1205476413, 1179446744, 1154022537, 1129187654, 1104926478, 1081223900, 1058065293, 1035436496, 1013323795, 991713905, 970593954, 949951464, 929774341, 910050859, 890769641, 871919654, 853490191, 835470860, 817851572, 800622534, 783774232, 767297427, 751183141, 735422650, 720007475, 704929374, 690180333, 675752556, 661638464, 647830682, 634322034, 621105537, 608174395, 595521991, 583141884, 571027800, 559173631, 547573426, 536221387, 525111867, 514239361, 503598505, 493184070, 482990959, 473014203, 463248955, 453690491, 444334201, 435175589, 426210271, 417433967, 408842502]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1119).prefactor = (2815241528780497/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1119).cutoff/(generalMeanRows 1119).c)).2 =
    (380777684944869/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1119).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1119).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1119).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1119

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1119).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1119).criticalRate j.val*(generalMeanRows 1119).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1119).c*(generalMeanRows 1119).criticalPoint j.val)).2-
      (generalMeanRows 1119).J/2-(generalMeanRows 1119).error (generalMeanGrid j.val)+
      (generalMeanRows 1119).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1119).c)).2-
      (generalMeanRows 1119).J/2-(generalMeanRows 1119).error 4 := by
  have he : (generalMeanRows 1119).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1119) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1119)
    prefactorDomain slopePositive criticalMargin finalMargin

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
