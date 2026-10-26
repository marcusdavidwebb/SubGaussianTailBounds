import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 1120. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1120
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6434077777, 6246881302, 6067153125, 5894484210, 5728494538, 5568830539, 5415162796, 5267184004, 5124607131, 4987163769, 4854602647, 4726688289, 4603199798, 4483929752, 4368683204, 4257276765, 4149537776, 4045303543, 3944420638, 3846744263, 3752137664, 3660471586, 3571623778, 3485478539, 3401926285, 3320863169, 3242190710, 3165815462, 3091648704, 3019606147, 2949607671, 2881577072, 2815441833, 2751132905, 2688584507, 2627733939, 2568521407, 2510889854, 2454784815, 2400154267, 2346948498, 2295119980, 2244623254, 2195414814, 2147453012, 2100697950, 2055111399, 2010656705, 1967298714, 1925003693, 1883739258, 1843474311, 1804178971, 1765824518, 1728383335, 1691828855, 1656135512, 1621278693, 1587234691, 1553980668, 1521494609, 1489755289, 1458742235, 1428435690, 1398816588, 1369866515, 1341567687, 1313902919, 1286855601, 1260409672, 1234549599, 1209260351, 1184527384, 1160336615, 1136674408, 1113527550, 1090883242, 1068729077, 1047053024, 1025843418, 1005088942, 984778614, 964901777, 945448083, 926407484, 907770222, 889526815, 871668048, 854184966, 837068862, 820311269, 803903952, 787838901, 772108319, 756704621, 741620421, 726848531, 712381948, 698213854, 684337605, 670746731, 657434925, 644396040, 631624084, 619113217, 606857742, 594852104, 583090886, 571568802, 560280697, 549221537, 538386413, 527770533, 517369217, 507177900, 497192120, 487407525, 477819860, 468424973, 459218807, 450197396]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1120).prefactor = (5290962243330371/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1120).cutoff/(generalMeanRows 1120).c)).2 =
    (420492347231433/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1120).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1120).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1120).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1120

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1120).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1120).criticalRate j.val*(generalMeanRows 1120).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1120).c*(generalMeanRows 1120).criticalPoint j.val)).2-
      (generalMeanRows 1120).J/2-(generalMeanRows 1120).error (generalMeanGrid j.val)+
      (generalMeanRows 1120).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1120).c)).2-
      (generalMeanRows 1120).J/2-(generalMeanRows 1120).error 4 := by
  have he : (generalMeanRows 1120).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1120) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1120)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1120

/-! Kernel-checked entropy margins for general spectral rectangle 1121. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1121
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6531274826, 6336308835, 6149186166, 5969478116, 5796786304, 5630739994, 5470993698, 5317225042, 5169132849, 5026435418, 4888868971, 4756186251, 4628155253, 4504558074, 4385189863, 4269857872, 4158380579, 4050586902, 3946315460, 3845413915, 3747738353, 3653152721, 3561528308, 3472743265, 3386682163, 3303235588, 3222299755, 3143776164, 3067571272, 2993596193, 2921766414, 2852001541, 2784225049, 2718364062, 2654349137, 2592114072, 2531595721, 2472733819, 2415470828, 2359751783, 2305524149, 2252737697, 2201344373, 2151298185, 2102555098, 2055072927, 2008811241, 1963731278, 1919795856, 1876969295, 1835217341, 1794507095, 1754806950, 1716086522, 1678316596, 1641469070, 1605516897, 1570434042, 1536195430, 1502776905, 1470155183, 1438307818, 1407213162, 1376850328, 1347199158, 1318240189, 1289954626, 1262324310, 1235331693, 1208959810, 1183192257, 1158013165, 1133407180, 1109359440, 1085855558, 1062881600, 1040424068, 1018469881, 997006364, 976021226, 955502549, 935438771, 915818676, 896631379, 877866313, 859513218, 841562132, 824003377, 806827549, 790025511, 773588382, 757507526, 741774547, 726381280, 711319780, 696582320, 682161378, 668049636, 654239966, 640725432, 627499278, 614554923, 601885960, 589486143, 577349388, 565469766, 553841498, 542458950, 531316630, 520409182, 509731384, 499278142, 489044488, 479025575, 469216673, 459613168, 450210558, 441004446, 431990543, 423164662, 414522714]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1121).prefactor = (1105709512679277/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1121).cutoff/(generalMeanRows 1121).c)).2 =
    (163677116791/400000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1121).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1121).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1121).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1121

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1121).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1121).criticalRate j.val*(generalMeanRows 1121).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1121).c*(generalMeanRows 1121).criticalPoint j.val)).2-
      (generalMeanRows 1121).J/2-(generalMeanRows 1121).error (generalMeanGrid j.val)+
      (generalMeanRows 1121).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1121).c)).2-
      (generalMeanRows 1121).J/2-(generalMeanRows 1121).error 4 := by
  have he : (generalMeanRows 1121).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1121) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1121)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1121

/-! Kernel-checked entropy margins for general spectral rectangle 1122. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1122
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6352224325, 6150683629, 5957432714, 5772019903, 5594025239, 5423057698, 5258752687, 5100769821, 4948790922, 4802518224, 4661672754, 4525992868, 4395232927, 4269162095, 4147563245, 4030231967, 3916975655, 3807612677, 3701971619, 3599890578, 3501216530, 3405804733, 3313518190, 3224227142, 3137808611, 3054145965, 2973128528, 2894651212, 2818614173, 2744922499, 2673485911, 2604218497, 2537038449, 2471867833, 2408632363, 2347261196, 2287686740, 2229844472, 2173672770, 2119112755, 2066108144, 2014605110, 1964552151, 1915899971, 1868601364, 1822611104, 1777885847, 1734384035, 1692065804, 1650892904, 1610828615, 1571837676, 1533886209, 1496941661, 1460972730, 1425949317, 1391842462, 1358624291, 1326267973, 1294747664, 1264038467, 1234116390, 1204958302, 1176541898, 1148845662, 1121848832, 1095531369, 1069873925, 1044857813, 1020464982, 996677988, 973479969, 950854622, 928786181, 907259394, 886259503, 865772224, 845783728, 826280626, 807249948, 788679131, 770555999, 752868753, 735605952, 718756506, 702309657, 686254969, 670582319, 655281882, 640344121, 625759780, 611519869, 597615659, 584038672, 570780671, 557833653, 545189840, 532841673, 520781804, 509003088, 497498579, 486261520, 475285339, 464563645, 454090216, 443859001, 433864111, 424099812, 414560523, 405240814, 396135393, 387239111, 378546951, 370054027, 361755582, 353646978, 345723700, 337981346, 330415628, 323022367, 315797490]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1122).prefactor = (722100176562053/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1122).cutoff/(generalMeanRows 1122).c)).2 =
    (95372547357041/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1122).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1122).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1122).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1122

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1122).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1122).criticalRate j.val*(generalMeanRows 1122).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1122).c*(generalMeanRows 1122).criticalPoint j.val)).2-
      (generalMeanRows 1122).J/2-(generalMeanRows 1122).error (generalMeanGrid j.val)+
      (generalMeanRows 1122).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1122).c)).2-
      (generalMeanRows 1122).J/2-(generalMeanRows 1122).error 4 := by
  have he : (generalMeanRows 1122).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1122) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1122)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1122

/-! Kernel-checked entropy margins for general spectral rectangle 1123. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1123
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6297975161, 6110457701, 5930512267, 5757719962, 5591691848, 5432066286, 5278506571, 5130698809, 4988350016, 4851186409, 4718951866, 4591406531, 4468325558, 4349497966, 4234725595, 4123822169, 4016612422, 3912931314, 3812623310, 3715541714, 3621548061, 3530511562, 3442308587, 3356822189, 3273941670, 3193562176, 3115584322, 3039913847, 2966461295, 2895141716, 2825874389, 2758582568, 2693193244, 2629636921, 2567847410, 2507761639, 2449319469, 2392463530, 2337139063, 2283293775, 2230877699, 2179843070, 2130144202, 2081737378, 2034580743, 1988634206, 1943859348, 1900219333, 1857678830, 1816203932, 1775762086, 1736322024, 1697853702, 1660328236, 1623717847, 1587995808, 1553136392, 1519114828, 1485907251, 1453490663, 1421842893, 1390942558, 1360769028, 1331302391, 1302523424, 1274413557, 1246954853, 1220129971, 1193922149, 1168315172, 1143293357, 1118841522, 1094944972, 1071589479, 1048761257, 1026446950, 1004633616, 983308703, 962460044, 942075833, 922144618, 902655284, 883597040, 864959410, 846732220, 828905585, 811469901, 794415836, 777734315, 761416518, 745453867, 729838018, 714560853, 699614474, 684991194, 670683532, 656684202, 642986111, 629582353, 616466198, 603631092, 591070648, 578778642, 566749010, 554975837, 543453361, 532175960, 521138154, 510334598, 499760079, 489409510, 479277930, 469360498, 459652488, 450149290, 440846404, 431739436, 422824099, 414096205, 405551667, 397186491]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1123).prefactor = (1356937562346067/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1123).cutoff/(generalMeanRows 1123).c)).2 =
    (217086225567757/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1123).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1123).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1123).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1123

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1123).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1123).criticalRate j.val*(generalMeanRows 1123).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1123).c*(generalMeanRows 1123).criticalPoint j.val)).2-
      (generalMeanRows 1123).J/2-(generalMeanRows 1123).error (generalMeanGrid j.val)+
      (generalMeanRows 1123).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1123).c)).2-
      (generalMeanRows 1123).J/2-(generalMeanRows 1123).error 4 := by
  have he : (generalMeanRows 1123).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1123) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1123)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1123

/-! Kernel-checked entropy margins for general spectral rectangle 1124. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1124
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6460010978, 6265238921, 6078366508, 5898957100, 5726605240, 5560933888, 5401591956, 5248252104, 5100608760, 4958376344, 4821287663, 4689092466, 4561556133, 4438458480, 4319592686, 4204764300, 4093790349, 3986498511, 3882726369, 3782320715, 3685136926, 3591038374, 3499895895, 3411587296, 3325996899, 3243015118, 3162538073, 3084467229, 3008709064, 2935174756, 2863779899, 2794444235, 2727091403, 2661648716, 2598046934, 2536220076, 2476105224, 2417642350, 2360774157, 2305445922, 2251605356, 2199202469, 2148189447, 2098520532, 2050151915, 2003041632, 1957149468, 1912436864, 1868866835, 1826403887, 1785013945, 1744664278, 1705323436, 1666961184, 1629548446, 1593057246, 1557460657, 1522732754, 1488848559, 1455784008, 1423515899, 1392021858, 1361280302, 1331270398, 1301972038, 1273365801, 1245432923, 1218155274, 1191515326, 1165496127, 1140081282, 1115254925, 1091001699, 1067306736, 1044155636, 1021534448, 999429653, 977828150, 956717232, 936084579, 915918240, 896206617, 876938455, 858102827, 839689125, 821687044, 804086575, 786877993, 770051846, 753598947, 737510363, 721777410, 706391639, 691344832, 676628994, 662236344, 648159309, 634390517, 620922791, 607749140, 594862760, 582257018, 569925455, 557861779, 546059856, 534513709, 523217511, 512165584, 501352389, 490772527, 480420732, 470291869, 460380927, 450683020, 441193381, 431907356, 422820407, 413928104, 405226121, 396710239, 388376338]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1124).prefactor = (2824203703778981/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1124).cutoff/(generalMeanRows 1124).c)).2 =
    (26792370738617/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1124).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1124).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1124).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1124

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1124).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1124).criticalRate j.val*(generalMeanRows 1124).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1124).c*(generalMeanRows 1124).criticalPoint j.val)).2-
      (generalMeanRows 1124).J/2-(generalMeanRows 1124).error (generalMeanGrid j.val)+
      (generalMeanRows 1124).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1124).c)).2-
      (generalMeanRows 1124).J/2-(generalMeanRows 1124).error 4 := by
  have he : (generalMeanRows 1124).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1124) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1124)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1124

/-! Kernel-checked entropy margins for general spectral rectangle 1125. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1125
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6347162863, 6146287406, 5953709496, 5768971611, 5591648715, 5421345383, 5257693241, 5100348675, 4948990776, 4803319493, 4663053967, 4527931025, 4397703816, 4272140580, 4151023515, 4034147758, 3921320451, 3812359882, 3707094707, 3605363230, 3507012746, 3411898934, 3319885302, 3230842670, 3144648696, 3061187441, 2980348958, 2902028922, 2826128280, 2752552924, 2681213400, 2612024619, 2544905608, 2479779260, 2416572113, 2355214143, 2295638561, 2237781637, 2181582527, 2126983113, 2073927852, 2022363640, 1972239677, 1923507348, 1876120103, 1830033355, 1785204372, 1741592186, 1699157502, 1657862614, 1617671323, 1578548868, 1540461850, 1503378169, 1467266958, 1432098530, 1397844317, 1364476819, 1331969554, 1300297014, 1269434616, 1239358665, 1210046308, 1181475505, 1153624985, 1126474218, 1100003380, 1074193325, 1049025554, 1024482190, 1000545950, 977200122, 954428541, 932215567, 910546064, 889405379, 868779325, 848654161, 829016575, 809853667, 791152935, 772902260, 755089889, 737704423, 720734805, 704170306, 688000516, 672215326, 656804927, 641759788, 627070659, 612728548, 598724725, 585050702, 571698232, 558659298, 545926107, 533491080, 521346847, 509486240, 497902286, 486588201, 475537385, 464743413, 454200034, 443901161, 433840870, 424013393, 414413113, 405034559, 395872405, 386921460, 378176670, 369633110, 361285982, 353130608, 345162433, 337377015, 329770025, 322337245, 315074560]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1125).prefactor = (2939017528060997/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1125).cutoff/(generalMeanRows 1125).c)).2 =
    (406996865756549/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1125).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1125).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1125).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1125

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1125).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1125).criticalRate j.val*(generalMeanRows 1125).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1125).c*(generalMeanRows 1125).criticalPoint j.val)).2-
      (generalMeanRows 1125).J/2-(generalMeanRows 1125).error (generalMeanGrid j.val)+
      (generalMeanRows 1125).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1125).c)).2-
      (generalMeanRows 1125).J/2-(generalMeanRows 1125).error 4 := by
  have he : (generalMeanRows 1125).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1125) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1125)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1125

/-! Kernel-checked entropy margins for general spectral rectangle 1126. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1126
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6266317458, 6079608245, 5900464232, 5728462102, 5563209179, 5404340699, 5251517372, 5104423203, 4962763535, 4826263291, 4694665390, 4567729315, 4445229814, 4326955728, 4212708920, 4102303300, 3995563943, 3892326273, 3792435325, 3695745064, 3602117763, 3511423426, 3423539270, 3338349231, 3255743522, 3175618221, 3097874887, 3022420207, 2949165676, 2878027286, 2808925254, 2741783753, 2676530681, 2613097427, 2551418668, 2491432171, 2433078614, 2376301418, 2321046586, 2267262559, 2214900077, 2163912053, 2114253450, 2065881171, 2018753952, 1972832265, 1928078226, 1884455507, 1841929256, 1800466020, 1760033675, 1720601357, 1682139398, 1644619270, 1608013525, 1572295748, 1537440500, 1503423276, 1470220462, 1437809288, 1406167795, 1375274793, 1345109831, 1315653158, 1286885698, 1258789013, 1231345284, 1204537277, 1178348323, 1152762290, 1127763564, 1103337025, 1079468031, 1056142391, 1033346356, 1011066595, 989290182, 968004577, 947197615, 926857490, 906972740, 887532238, 868525175, 849941052, 831769668, 814001106, 796625730, 779634169, 763017308, 746766285, 730872474, 715327486, 700123152, 685251524, 670704863, 656475632, 642556491, 628940293, 615620073, 602589045, 589840597, 577368285, 565165826, 553227098, 541546129, 530117096, 518934323, 507992271, 497285538, 486808854, 476557077, 466525189, 456708296, 447101617, 437700490, 428500361, 419496787, 410685427, 402062045, 393622504, 385362764]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1126).prefactor = (5521375740540297/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1126).cutoff/(generalMeanRows 1126).c)).2 =
    (229446619213911/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1126).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1126).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1126).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1126

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1126).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1126).criticalRate j.val*(generalMeanRows 1126).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1126).c*(generalMeanRows 1126).criticalPoint j.val)).2-
      (generalMeanRows 1126).J/2-(generalMeanRows 1126).error (generalMeanGrid j.val)+
      (generalMeanRows 1126).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1126).c)).2-
      (generalMeanRows 1126).J/2-(generalMeanRows 1126).error 4 := by
  have he : (generalMeanRows 1126).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1126) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1126)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1126

/-! Kernel-checked entropy margins for general spectral rectangle 1127. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1127
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6593332085, 6399348882, 6213190535, 6034418771, 5862627088, 5697437928, 5538500143, 5385486736, 5238092829, 5096033843, 4959043851, 4826874089, 4699291618, 4576078098, 4457028683, 4341951008, 4230664273, 4122998398, 4018793256, 3917897969, 3820170257, 3725475853, 3633687945, 3544686686, 3458358720, 3374596759, 3293299188, 3214369698, 3137716950, 3063254258, 2990899301, 2920573856, 2852203542, 2785717591, 2721048630, 2658132482, 2596907975, 2537316770, 2479303195, 2422814095, 2367798689, 2314208439, 2261996921, 2211119715, 2161534290, 2113199908, 2066077523, 2020129697, 1975320511, 1931615489, 1888981524, 1847386809, 1806800767, 1767193997, 1728538209, 1690806177, 1653971680, 1618009458, 1582895168, 1548605337, 1515117325, 1482409283, 1450460121, 1419249472, 1388757659, 1358965667, 1329855112, 1301408213, 1273607768, 1246437130, 1219880184, 1193921320, 1168545419, 1143737829, 1119484349, 1095771208, 1072585051, 1049912919, 1027742239, 1006060806, 984856769, 964118618, 943835174, 923995574, 904589259, 885605967, 867035719, 848868810, 831095800, 813707504, 796694985, 780049545, 763762714, 747826249, 732232119, 716972505, 702039787, 687426544, 673125542, 659129731, 645432241, 632026373, 618905593, 606063534, 593493984, 581190882, 569148318, 557360525, 545821876, 534526880, 523470176, 512646535, 502050848, 491678132, 481523518, 471582254, 461849699, 452321318, 442992686, 433859477, 424917468]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1127).prefactor = (5725996296051141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1127).cutoff/(generalMeanRows 1127).c)).2 =
    (46429865699473/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1127).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1127).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1127).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1127

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1127).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1127).criticalRate j.val*(generalMeanRows 1127).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1127).c*(generalMeanRows 1127).criticalPoint j.val)).2-
      (generalMeanRows 1127).J/2-(generalMeanRows 1127).error (generalMeanGrid j.val)+
      (generalMeanRows 1127).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1127).c)).2-
      (generalMeanRows 1127).J/2-(generalMeanRows 1127).error 4 := by
  have he : (generalMeanRows 1127).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1127) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1127)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1127

/-! Kernel-checked entropy margins for general spectral rectangle 1128. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1128
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7039180086, 6837363598, 6643617416, 6457488477, 6278556675, 6106431907, 5940751456, 5781177635, 5627395688, 5479111888, 5336051838, 5197958921, 5064592907, 4935728688, 4811155126, 4690674003, 4574099071, 4461255174, 4351977453, 4246110612, 4143508254, 4044032255, 3947552205, 3853944887, 3763093788, 3674888666, 3589225132, 3506004276, 3425132314, 3346520266, 3270083651, 3195742210, 3123419650, 3053043394, 2984544366, 2917856779, 2852917939, 2789668066, 2728050126, 2668009671, 2609494692, 2552455487, 2496844524, 2442616329, 2389727365, 2338135938, 2287802087, 2238687499, 2190755420, 2143970573, 2098299082, 2053708403, 2010167251, 1967645544, 1926114335, 1885545764, 1845913001, 1807190195, 1769352433, 1732375688, 1696236784, 1660913354, 1626383803, 1592627272, 1559623607, 1527353328, 1495797597, 1464938191, 1434757477, 1405238385, 1376364385, 1348119465, 1320488110, 1293455280, 1267006392, 1241127302, 1215804287, 1191024028, 1166773599, 1143040443, 1119812368, 1097077525, 1074824402, 1053041808, 1031718861, 1010844978, 990409866, 970403509, 950816161, 931638334, 912860791, 894474538, 876470815, 858841088, 841577041, 824670572, 808113785, 791898979, 776018649, 760465475, 745232319, 730312217, 715698375, 701384165, 687363119, 673628923, 660175417, 646996583, 634086549, 621439579, 609050074, 596912562, 585021702, 573372274, 561959178, 550777433, 539822170, 529088632, 518572168, 508268235, 498172388]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1128).prefactor = (2969100014481443/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1128).cutoff/(generalMeanRows 1128).c)).2 =
    (95039589490553/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1128).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1128).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1128).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1128

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1128).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1128).criticalRate j.val*(generalMeanRows 1128).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1128).c*(generalMeanRows 1128).criticalPoint j.val)).2-
      (generalMeanRows 1128).J/2-(generalMeanRows 1128).error (generalMeanGrid j.val)+
      (generalMeanRows 1128).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1128).c)).2-
      (generalMeanRows 1128).J/2-(generalMeanRows 1128).error 4 := by
  have he : (generalMeanRows 1128).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1128) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1128)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1128

/-! Kernel-checked entropy margins for general spectral rectangle 1129. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1129
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7515997411, 7306167120, 7104657938, 6911001437, 6724763370, 6545540609, 6372958422, 6206668034, 6046344436, 5891684423, 5742404816, 5598240865, 5458944798, 5324284504, 5194042343, 5068014052, 4946007760, 4827843079, 4713350274, 4602369509, 4494750146, 4390350108, 4289035293, 4190679030, 4095161580, 4002369680, 3912196114, 3824539322, 3739303036, 3656395944, 3575731375, 3497227017, 3420804638, 3346389844, 3273911845, 3203303237, 3134499802, 3067440322, 3002066402, 2938322309, 2876154817, 2815513069, 2756348441, 2698614417, 2642266477, 2587261985, 2533560087, 2481121618, 2429909009, 2379886206, 2331018591, 2283272907, 2236617187, 2191020692, 2146453849, 2102888191, 2060296304, 2018651777, 1977929153, 1938103881, 1899152279, 1861051486, 1823779433, 1787314798, 1751636978, 1716726056, 1682562768, 1649128476, 1616405144, 1584375306, 1553022046, 1522328976, 1492280209, 1462860343, 1434054441, 1405848010, 1378226985, 1351177712, 1324686931, 1298741762, 1273329692, 1248438558, 1224056536, 1200172127, 1176774148, 1153851719, 1131394250, 1109391436, 1087833241, 1066709896, 1046011881, 1025729925, 1005854993, 986378279, 967291199, 948585384, 930252674, 912285108, 894674922, 877414540, 860496570, 843913797, 827659178, 811725840, 796107068, 780796308, 765787157, 751073362, 736648813, 722507542, 708643717, 695051637, 681725732, 668660558, 655850790, 643291226, 630976776, 618902465, 607063428, 595454904, 584072241]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1129).prefactor = (1231653593918423/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1129).cutoff/(generalMeanRows 1129).c)).2 =
    (60777167837797/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1129).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1129).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1129).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1129

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1129).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1129).criticalRate j.val*(generalMeanRows 1129).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1129).c*(generalMeanRows 1129).criticalPoint j.val)).2-
      (generalMeanRows 1129).J/2-(generalMeanRows 1129).error (generalMeanGrid j.val)+
      (generalMeanRows 1129).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1129).c)).2-
      (generalMeanRows 1129).J/2-(generalMeanRows 1129).error 4 := by
  have he : (generalMeanRows 1129).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1129) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1129)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1129

/-! Kernel-checked entropy margins for general spectral rectangle 1130. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1130
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8026908166, 7811904248, 7605327425, 7406700930, 7215582948, 7031563490, 6854261599, 6683322848, 6518417100, 6359236498, 6205493643, 6056919957, 5913264199, 5774291116, 5639780224, 5509524688, 5383330313, 5261014613, 5142405964, 5027342828, 4915673040, 4807253152, 4701947836, 4599629326, 4500176910, 4403476460, 4309419994, 4217905281, 4128835459, 4042118703, 3957667896, 3875400339, 3795237473, 3717104629, 3640930783, 3566648344, 3494192942, 3423503241, 3354520758, 3287189699, 3221456801, 3157271191, 3094584247, 3033349475, 2973522386, 2915060390, 2857922690, 2802070186, 2747465382, 2694072304, 2641856415, 2590784546, 2540824821, 2491946593, 2444120381, 2397317810, 2351511560, 2306675309, 2262783689, 2219812237, 2177737354, 2136536262, 2096186966, 2056668221, 2017959491, 1980040924, 1942893318, 1906498090, 1870837255, 1835893392, 1801649627, 1768089607, 1735197474, 1702957854, 1671355827, 1640376915, 1610007061, 1580232616, 1551040319, 1522417282, 1494350980, 1466829233, 1439840194, 1413372338, 1387414450, 1361955611, 1336985192, 1312492839, 1288468467, 1264902250, 1241784610, 1219106211, 1196857949, 1175030947, 1153616544, 1132606292, 1111991947, 1091765460, 1071918977, 1052444827, 1033335521, 1014583744, 996182349, 978124356, 960402940, 943011436, 925943327, 909192240, 892751948, 876616359, 860779517, 845235596, 829978897, 815003845, 800304983, 785876975, 771714597, 757812735, 744166386, 730770650, 717620732]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1130).prefactor = (393387771885161/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1130).cutoff/(generalMeanRows 1130).c)).2 =
    (251488755779919/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1130).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1130).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1130).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1130

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1130).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1130).criticalRate j.val*(generalMeanRows 1130).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1130).c*(generalMeanRows 1130).criticalPoint j.val)).2-
      (generalMeanRows 1130).J/2-(generalMeanRows 1130).error (generalMeanGrid j.val)+
      (generalMeanRows 1130).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1130).c)).2-
      (generalMeanRows 1130).J/2-(generalMeanRows 1130).error 4 := by
  have he : (generalMeanRows 1130).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1130) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1130)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1130

/-! Kernel-checked entropy margins for general spectral rectangle 1131. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1131
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5563957708, 5378029386, 5200019657, 5029482354, 4866003562, 4709198745, 4558710181, 4414204671, 4275371479, 4141920483, 4013580502, 3890097792, 3771234679, 3656768319, 3546489576, 3440201991, 3337720854, 3238872349, 3143492768, 3051427805, 2962531893, 2876667604, 2793705096, 2713521604, 2636000968, 2561033200, 2488514085, 2418344812, 2350431627, 2284685521, 2221021935, 2159360483, 2099624706, 2041741829, 1985642551, 1931260831, 1878533709, 1827401119, 1777805733, 1729692801, 1683010011, 1637707353, 1593736992, 1551053154, 1509612014, 1469371592, 1430291657, 1392333639, 1355460540, 1319636856, 1284828503, 1251002744, 1218128125, 1186174410, 1155112525, 1124914502, 1095553425, 1067003382, 1039239418, 1012237494, 985974441, 960427923, 935576402, 911399099, 887875964, 864987643, 842715449, 821041334, 799947862, 779418182, 759436008, 739985592, 721051704, 702619611, 684675059, 667204252, 650193835, 633630878, 617502858, 601797646, 586503490, 571609002, 557103146, 542975222, 529214857, 515811991, 502756869, 490040027, 477652281, 465584723, 453828705, 442375834, 431217963, 420347182, 409755808, 399436382, 389381658, 379584600, 370038368, 360736319, 351671999, 342839133, 334231624, 325843546, 317669137, 309702795, 301939076, 294372683, 286998466, 279811418, 272806668, 265979478, 259325239, 252839467, 246517801, 240355997, 234349924, 228495565, 222789008, 217226449, 211804184]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1131).prefactor = (5765701042255661/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1131).cutoff/(generalMeanRows 1131).c)).2 =
    (17396961932593/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1131).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1131).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1131).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1131

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1131).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1131).criticalRate j.val*(generalMeanRows 1131).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1131).c*(generalMeanRows 1131).criticalPoint j.val)).2-
      (generalMeanRows 1131).J/2-(generalMeanRows 1131).error (generalMeanGrid j.val)+
      (generalMeanRows 1131).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1131).c)).2-
      (generalMeanRows 1131).J/2-(generalMeanRows 1131).error 4 := by
  have he : (generalMeanRows 1131).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1131) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1131)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1131

/-! Kernel-checked entropy margins for general spectral rectangle 1132. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1132
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5657649098, 5468589932, 5287582700, 5114173722, 4947942114, 4788496863, 4635474225, 4488535389, 4347364387, 4211666212, 4081165116, 3955603083, 3834738436, 3718344579, 3606208854, 3498131494, 3393924679, 3293411665, 3196425990, 3102810746, 3012417917, 2925107761, 2840748249, 2759214548, 2680388543, 2604158394, 2530418132, 2459067279, 2390010505, 2323157302, 2258421686, 2195721918, 2134980251, 2076122686, 2019078752, 1963781300, 1910166306, 1858172695, 1807742174, 1758819069, 1711350189, 1665284680, 1620573903, 1577171312, 1535032345, 1494114315, 1454376314, 1415779122, 1378285117, 1341858199, 1306463709, 1272068358, 1238640164, 1206148381, 1174563445, 1143856918, 1114001430, 1084970634, 1056739153, 1029282544, 1002577248, 976600553, 951330557, 926746133, 902826892, 879553155, 856905920, 834866835, 813418170, 792542792, 772224138, 752446197, 733193481, 714451011, 696204291, 678439293, 661142438, 644300578, 627900979, 611931307, 596379612, 581234316, 566484196, 552118372, 538126297, 524497741, 511222784, 498291803, 485695460, 473424696, 461470719, 449824994, 438479235, 427425401, 416655679, 406162484, 395938450, 385976418, 376269438, 366810752, 357593798, 348612196, 339859745, 331330420, 323018362, 314917876, 307023423, 299329619, 291831228, 284523158, 277400455, 270458302, 263692012, 257097027, 250668910, 244403347, 238296138, 232343198, 226540549, 220884322, 215370751]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1132).prefactor = (5862789584638511/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1132).cutoff/(generalMeanRows 1132).c)).2 =
    (17396961932593/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1132).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1132).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1132).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1132

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1132).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1132).criticalRate j.val*(generalMeanRows 1132).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1132).c*(generalMeanRows 1132).criticalPoint j.val)).2-
      (generalMeanRows 1132).J/2-(generalMeanRows 1132).error (generalMeanGrid j.val)+
      (generalMeanRows 1132).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1132).c)).2-
      (generalMeanRows 1132).J/2-(generalMeanRows 1132).error 4 := by
  have he : (generalMeanRows 1132).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1132) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1132)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1132

/-! Kernel-checked entropy margins for general spectral rectangle 1133. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1133
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6809868279, 6606367508, 6411004158, 6223337914, 6042959397, 5869487426, 5702566583, 5541865036, 5387072587, 5237898921, 5094072023, 4955336752, 4821453554, 4692197285, 4567356150, 4446730733, 4330133110, 4217386045, 4108322243, 4002783676, 3900620955, 3801692761, 3705865313, 3613011880, 3523012334, 3435752729, 3351124921, 3269026206, 3189358994, 3112030495, 3036952437, 2964040802, 2893215570, 2824400499, 2757522901, 2692513445, 2629305967, 2567837297, 2508047092, 2449877683, 2393273932, 2338183096, 2284554700, 2232340416, 2181493957, 2131970967, 2083728923, 2036727042, 1990926198, 1946288833, 1902778883, 1860361706, 1819004008, 1778673786, 1739340259, 1700973814, 1663545950, 1627029227, 1591397216, 1556624454, 1522686399, 1489559389, 1457220603, 1425648022, 1394820398, 1364717215, 1335318662, 1306605600, 1278559534, 1251162587, 1224397473, 1198247473, 1172696412, 1147728636, 1123328992, 1099482807, 1076175870, 1053394412, 1031125091, 1009354974, 988071522, 967262575, 946916336, 927021360, 907566539, 888541093, 869934551, 851736747, 833937806, 816528134, 799498407, 782839563, 766542794, 750599533, 735001451, 719740444, 704808631, 690198340, 675902107, 661912666, 648222943, 634826050, 621715281, 608884101, 596326148, 584035219, 572005274, 560230425, 548704931, 537423198, 526379773, 515569335, 504986699, 494626805, 484484720, 474555630, 464834837, 455317760, 445999927, 436876973, 427944637]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1133).prefactor = (2851353941702541/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1133).cutoff/(generalMeanRows 1133).c)).2 =
    (392932271105719/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1133).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1133).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1133).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1133

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1133).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1133).criticalRate j.val*(generalMeanRows 1133).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1133).c*(generalMeanRows 1133).criticalPoint j.val)).2-
      (generalMeanRows 1133).J/2-(generalMeanRows 1133).error (generalMeanGrid j.val)+
      (generalMeanRows 1133).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1133).c)).2-
      (generalMeanRows 1133).J/2-(generalMeanRows 1133).error 4 := by
  have he : (generalMeanRows 1133).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1133) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1133)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1133

/-! Kernel-checked entropy margins for general spectral rectangle 1134. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1134
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6459919572, 6274472505, 6096383588, 5925248454, 5760691571, 5602363682, 5449939525, 5303115794, 5161609306, 5025155364, 4893506272, 4766429997, 4643708961, 4525138941, 4410528070, 4299695928, 4192472713, 4088698483, 3988222460, 3890902398, 3796603995, 3705200357, 3616571505, 3530603918, 3447190112, 3366228255, 3287621801, 3211279166, 3137113410, 3065041959, 2994986334, 2926871907, 2860627671, 2796186024, 2733482571, 2672455941, 2613047607, 2555201733, 2498865013, 2443986539, 2390517661, 2338411869, 2287624673, 2238113495, 2189837570, 2142757846, 2096836898, 2052038839, 2008329248, 1965675087, 1924044637, 1883407430, 1843734186, 1804996756, 1767168067, 1730222067, 1694133680, 1658878756, 1624434032, 1590777085, 1557886297, 1525740818, 1494320529, 1463606010, 1433578511, 1404219917, 1375512728, 1347440025, 1319985448, 1293133173, 1266867889, 1241174776, 1216039483, 1191448112, 1167387198, 1143843692, 1120804944, 1098258685, 1076193017, 1054596397, 1033457618, 1012765806, 992510397, 972681134, 953268051, 934261464, 915651958, 897430384, 879587840, 862115672, 845005459, 828249006, 811838337, 795765690, 780023504, 764604419, 749501265, 734707054, 720214982, 706018415, 692110887, 678486094, 665137891, 652060285, 639247430, 626693623, 614393301, 602341035, 590531528, 578959609, 567620230, 556508464, 545619499, 534948638, 524491290, 514242974, 504199313, 494356029, 484708942, 475253970, 465987121]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1134).prefactor = (2639987282904693/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1134).cutoff/(generalMeanRows 1134).c)).2 =
    (86915796549789/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1134).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1134).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1134).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1134

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1134).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1134).criticalRate j.val*(generalMeanRows 1134).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1134).c*(generalMeanRows 1134).criticalPoint j.val)).2-
      (generalMeanRows 1134).J/2-(generalMeanRows 1134).error (generalMeanGrid j.val)+
      (generalMeanRows 1134).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1134).c)).2-
      (generalMeanRows 1134).J/2-(generalMeanRows 1134).error 4 := by
  have he : (generalMeanRows 1134).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1134) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1134)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1134

/-! Kernel-checked entropy margins for general spectral rectangle 1135. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1135
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6576946380, 6383206590, 6197218399, 6018556755, 5846826824, 5681661315, 5522718085, 5369678013, 5222243077, 5080134640, 4943091898, 4810870476, 4683241167, 4559988775, 4440911075, 4325817857, 4214530059, 4106878972, 4002705516, 3901859568, 3804199356, 3709590896, 3617907467, 3529029144, 3442842348, 3359239445, 3278118366, 3199382262, 3122939174, 3048701739, 2976586910, 2906515695, 2838412919, 2772206996, 2707829724, 2645216086, 2584304072, 2525034506, 2467350889, 2411199249, 2356528004, 2303287829, 2251431539, 2200913968, 2151691868, 2103723805, 2056970065, 2011392565, 1966954772, 1923621622, 1881359445, 1840135901, 1799919907, 1760681581, 1722392184, 1685024061, 1648550591, 1612946141, 1578186017, 1544246418, 1511104403, 1478737844, 1447125391, 1416246441, 1386081101, 1356610158, 1327815050, 1299677836, 1272181172, 1245308286, 1219042949, 1193369459, 1168272614, 1143737698, 1119750452, 1096297063, 1073364147, 1050938725, 1029008214, 1007560410, 986583470, 966065904, 945996556, 926364599, 907159513, 888371084, 869989384, 852004767, 834407857, 817189537, 800340943, 783853453, 767718678, 751928457, 736474847, 721350117, 706546739, 692057385, 677874916, 663992381, 650403006, 637100191, 624077505, 611328680, 598847605, 586628323, 574665024, 562952046, 551483861, 540255081, 529260448, 518494832, 507953226, 497630746, 487522622, 477624201, 467930938, 458438397, 449142246, 440038254, 431122290]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1135).prefactor = (5532869684269881/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1135).cutoff/(generalMeanRows 1135).c)).2 =
    (52929600774463/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1135).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1135).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1135).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1135

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1135).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1135).criticalRate j.val*(generalMeanRows 1135).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1135).c*(generalMeanRows 1135).criticalPoint j.val)).2-
      (generalMeanRows 1135).J/2-(generalMeanRows 1135).error (generalMeanGrid j.val)+
      (generalMeanRows 1135).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1135).c)).2-
      (generalMeanRows 1135).J/2-(generalMeanRows 1135).error 4 := by
  have he : (generalMeanRows 1135).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1135) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1135)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1135

/-! Kernel-checked entropy margins for general spectral rectangle 1136. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1136
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6508284059, 6306861158, 6113640845, 5928174719, 5750046070, 5578867081, 5414276324, 5255936535, 5103532605, 4956769783, 4815372053, 4679080669, 4547652825, 4420860458, 4298489144, 4180337108, 4066214314, 3955941628, 3849350062, 3746280074, 3646580925, 3550110093, 3456732727, 3366321146, 3278754380, 3193917740, 3111702424, 3032005150, 2954727818, 2879777191, 2807064609, 2736505711, 2668020183, 2601531525, 2536966828, 2474256568, 2413334419, 2354137069, 2296604057, 2240677613, 2186302513, 2133425943, 2081997367, 2031968412, 1983292746, 1935925982, 1889825570, 1844950708, 1801262248, 1758722623, 1717295756, 1676946998, 1637643051, 1599351905, 1562042777, 1525686051, 1490253226, 1455716859, 1422050521, 1389228748, 1357226999, 1326021611, 1295589762, 1265909435, 1236959381, 1208719085, 1181168736, 1154289196, 1128061972, 1102469187, 1077493559, 1053118370, 1029327449, 1006105147, 983436314, 961306285, 939700853, 918606259, 898009170, 877896662, 858256209, 839075661, 820343238, 802047510, 784177387, 766722106, 749671217, 733014578, 716742337, 700844924, 685313045, 670137667, 655310011, 640821546, 626663975, 612829233, 599309476, 586097074, 573184605, 560564847, 548230773, 536175542, 524392498, 512875160, 501617215, 490612521, 479855091, 469339097, 459058860, 449008847, 439183669, 429578072, 420186936, 411005272, 402028215, 393251024, 384669076, 376277862, 368072986, 360050162, 352205207]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1136).prefactor = (5797877728681811/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1136).cutoff/(generalMeanRows 1136).c)).2 =
    (401518120488057/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1136).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1136).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1136).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1136

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1136).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1136).criticalRate j.val*(generalMeanRows 1136).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1136).c*(generalMeanRows 1136).criticalPoint j.val)).2-
      (generalMeanRows 1136).J/2-(generalMeanRows 1136).error (generalMeanGrid j.val)+
      (generalMeanRows 1136).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1136).c)).2-
      (generalMeanRows 1136).J/2-(generalMeanRows 1136).error 4 := by
  have he : (generalMeanRows 1136).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1136) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1136)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1136

/-! Kernel-checked entropy margins for general spectral rectangle 1137. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1137
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6350756521, 6165765695, 5988177181, 5817579816, 5653592051, 5495859318, 5344051674, 5197861702, 5057002620, 4921206593, 4790223194, 4663818035, 4541771506, 4423877652, 4309943132, 4199786290, 4093236295, 3990132356, 3890323015, 3793665484, 3700025047, 3609274507, 3521293675, 3435968906, 3353192664, 3272863123, 3194883799, 3119163211, 3045614562, 2974155448, 2904707584, 2837196559, 2771551591, 2707705319, 2645593593, 2585155291, 2526332137, 2469068542, 2413311446, 2359010181, 2306116331, 2254583610, 2204367744, 2155426362, 2107718895, 2061206476, 2015851852, 1971619302, 1928474550, 1886384700, 1845318158, 1805244571, 1766134763, 1727960675, 1690695315, 1654312701, 1618787816, 1584096560, 1550215707, 1517122866, 1484796438, 1453215585, 1422360193, 1392210837, 1362748755, 1333955816, 1305814492, 1278307834, 1251419446, 1225133461, 1199434520, 1174307752, 1149738750, 1125713556, 1102218642, 1079240891, 1056767583, 1034786380, 1013285308, 992252745, 971677411, 951548348, 931854914, 912586769, 893733864, 875286433, 857234979, 839570266, 822283312, 805365378, 788807959, 772602779, 756741782, 741217122, 726021160, 711146455, 696585759, 682332010, 668378326, 654717998, 641344490, 628251426, 615432590, 602881922, 590593508, 578561583, 566780519, 555244827, 543949150, 532888259, 522057052, 511450546, 501063878, 490892299, 480931173, 471175971, 461622271, 452265752, 443102195, 434127476, 425337569]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1137).prefactor = (1347267958282849/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1137).cutoff/(generalMeanRows 1137).c)).2 =
    (226736466054453/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1137).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1137).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1137).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1137

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1137).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1137).criticalRate j.val*(generalMeanRows 1137).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1137).c*(generalMeanRows 1137).criticalPoint j.val)).2-
      (generalMeanRows 1137).J/2-(generalMeanRows 1137).error (generalMeanGrid j.val)+
      (generalMeanRows 1137).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1137).c)).2-
      (generalMeanRows 1137).J/2-(generalMeanRows 1137).error 4 := by
  have he : (generalMeanRows 1137).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1137) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1137)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1137

/-! Kernel-checked entropy margins for general spectral rectangle 1138. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1138
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6434580094, 6242353188, 6057886262, 5880749126, 5710542481, 5546895172, 5389461737, 5237920219, 5091970197, 4951331023, 4815740230, 4684952088, 4558736309, 4436876860, 4319170895, 4205427769, 4095468155, 3989123222, 3886233893, 3786650163, 3690230467, 3596841109, 3506355727, 3418654807, 3333625234, 3251159872, 3171157182, 3093520867, 3018159539, 2944986418, 2873919043, 2804879015, 2737791747, 2672586240, 2609194870, 2547553189, 2487599743, 2429275900, 2372525690, 2317295655, 2263534707, 2211194002, 2160226812, 2110588416, 2062235985, 2015128491, 1969226605, 1924492609, 1880890317, 1838384994, 1796943281, 1756533130, 1717123735, 1678685472, 1641189843, 1604609420, 1568917794, 1534089527, 1500100106, 1466925901, 1434544124, 1402932790, 1372070680, 1341937310, 1312512896, 1283778321, 1255715113, 1228305411, 1201531941, 1175377991, 1149827389, 1124864479, 1100474102, 1076641572, 1053352661, 1030593580, 1008350960, 986611837, 965363636, 944594157, 924291559, 904444350, 885041370, 866071781, 847525055, 829390964, 811659567, 794321201, 777366472, 760786246, 744571637, 728714002, 713204932, 698036243, 683199969, 668688357, 654493857, 640609116, 627026975, 613740459, 600742772, 588027292, 575587569, 563417312, 551510392, 539860832, 528462805, 517310628, 506398761, 495721798, 485274467, 475051623, 465048249, 455259447, 445680439, 436306560, 427133258, 418156091, 409370719, 400772907, 392358521]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1138).prefactor = (5619689955288341/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1138).cutoff/(generalMeanRows 1138).c)).2 =
    (442632717556041/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1138).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1138).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1138).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1138

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1138).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1138).criticalRate j.val*(generalMeanRows 1138).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1138).c*(generalMeanRows 1138).criticalPoint j.val)).2-
      (generalMeanRows 1138).J/2-(generalMeanRows 1138).error (generalMeanGrid j.val)+
      (generalMeanRows 1138).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1138).c)).2-
      (generalMeanRows 1138).J/2-(generalMeanRows 1138).error 4 := by
  have he : (generalMeanRows 1138).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1138) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1138)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1138

/-! Kernel-checked entropy margins for general spectral rectangle 1139. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1139
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6520254067, 6320624814, 6129128100, 5945313764, 5768763871, 5599089851, 5435929947, 5278946932, 5127826064, 4982273242, 4842013348, 4706788751, 4576357945, 4450494319, 4328985042, 4211630038, 4098241060, 3988640837, 3882662301, 3780147872, 3680948803, 3584924581, 3491942371, 3401876512, 3314608040, 3230024257, 3148018332, 3068488925, 2991339847, 2916479738, 2843821772, 2773283384, 2704786011, 2638254858, 2573618672, 2510809541, 2449762697, 2390416339, 2332711464, 2276591715, 2222003226, 2168894493, 2117216242, 2066921310, 2017964531, 1970302634, 1923894140, 1878699271, 1834679862, 1791799281, 1750022348, 1709315266, 1669645553, 1630981973, 1593294481, 1556554163, 1520733182, 1485804730, 1451742975, 1418523022, 1386120865, 1354513348, 1323678131, 1293593647, 1264239073, 1235594294, 1207639877, 1180357036, 1153727609, 1127734032, 1102359310, 1077586998, 1053401177, 1029786430, 1006727828, 984210905, 962221643, 940746454, 919772163, 899285990, 879275543, 859728792, 840634066, 821980034, 803755694, 785950362, 768553660, 751555504, 734946097, 718715915, 702855701, 687356453, 672209419, 657406086, 642938171, 628797617, 614976583, 601467437, 588262751, 575355293, 562738023, 550404083, 538346795, 526559653, 515036322, 503770625, 492756548, 481988226, 471459945, 461166135, 451101365, 441260341, 431637902, 422229012, 413028763, 404032367, 395235153, 386632565, 378220159, 369993597, 361948649]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1139).prefactor = (5860177071571539/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1139).cutoff/(generalMeanRows 1139).c)).2 =
    (86381750838613/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1139).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1139).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1139).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1139

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1139).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1139).criticalRate j.val*(generalMeanRows 1139).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1139).c*(generalMeanRows 1139).criticalPoint j.val)).2-
      (generalMeanRows 1139).J/2-(generalMeanRows 1139).error (generalMeanGrid j.val)+
      (generalMeanRows 1139).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1139).c)).2-
      (generalMeanRows 1139).J/2-(generalMeanRows 1139).error 4 := by
  have he : (generalMeanRows 1139).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1139) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1139)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1139

/-! Kernel-checked entropy margins for general spectral rectangle 1140. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1140
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6307466626, 6124023131, 5947931151, 5778777647, 5616179730, 5459781960, 5309253941, 5164288159, 5024598054, 4889916280, 4759993137, 4634595160, 4513503837, 4396514446, 4283435003, 4174085298, 4068296026, 3965907981, 3866771331, 3770744944, 3677695778, 3587498318, 3500034056, 3415191014, 3332863310, 3252950746, 3175358440, 3099996479, 3026779598, 2955626887, 2886461515, 2819210474, 2753804348, 2690177093, 2628265828, 2568010651, 2509354463, 2452242801, 2396623685, 2342447478, 2289666751, 2238236157, 2188112320, 2139253720, 2091620596, 2045174850, 1999879957, 1955700880, 1912603997, 1870557022, 1829528939, 1789489937, 1750411351, 1712265600, 1675026140, 1638667407, 1603164774, 1568494505, 1534633713, 1501560318, 1469253015, 1437691232, 1406855101, 1376725425, 1347283650, 1318511834, 1290392622, 1262909221, 1236045376, 1209785348, 1184113889, 1159016228, 1134478046, 1110485463, 1087025014, 1064083640, 1041648666, 1019707791, 998249072, 977260907, 956732031, 936651493, 917008653, 897793168, 878994979, 860604305, 842611630, 825007697, 807783497, 790930259, 774439447, 758302748, 742512067, 727059519, 711937420, 697138286, 682654823, 668479919, 654606645, 641028244, 627738125, 614729863, 601997191, 589533995, 577334310, 565392317, 553702336, 542258824, 531056373, 520089701, 509353654, 498843198, 488553418, 478479515, 468616803, 458960703, 449506745, 440250560, 431187881, 422314539, 413626461]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1140).prefactor = (436739733977/80000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1140).cutoff/(generalMeanRows 1140).c)).2 =
    (240349459181249/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1140).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1140).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1140).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1140

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1140).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1140).criticalRate j.val*(generalMeanRows 1140).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1140).c*(generalMeanRows 1140).criticalPoint j.val)).2-
      (generalMeanRows 1140).J/2-(generalMeanRows 1140).error (generalMeanGrid j.val)+
      (generalMeanRows 1140).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1140).c)).2-
      (generalMeanRows 1140).J/2-(generalMeanRows 1140).error 4 := by
  have he : (generalMeanRows 1140).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1140) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1140)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1140

/-! Kernel-checked entropy margins for general spectral rectangle 1141. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1141
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6457344347, 6267152362, 6084616898, 5909308223, 5740827923, 5578806101, 5422898872, 5272786129, 5128169533, 4988770715, 4854329643, 4724603155, 4599363635, 4478397800, 4361505609, 4248499266, 4139202309, 4033448783, 3931082481, 3831956245, 3735931336, 3642876842, 3552669145, 3465191424, 3380333200, 3297989914, 3218062542, 3140457231, 3065084973, 2991861293, 2920705965, 2851542751, 2784299154, 2718906187, 2655298169, 2593412519, 2533189579, 2474572444, 2417506797, 2361940766, 2307824782, 2255111452, 2203755438, 2153713342, 2104943601, 2057406390, 2011063526, 1965878385, 1921815816, 1878842068, 1836924719, 1796032604, 1756135758, 1717205349, 1679213630, 1642133882, 1605940364, 1570608267, 1536113674, 1502433510, 1469545513, 1437428189, 1406060781, 1375423235, 1345496171, 1316260849, 1287699147, 1259793530, 1232527028, 1205883211, 1179846165, 1154400476, 1129531203, 1105223867, 1081464424, 1058239254, 1035535144, 1013339269, 991639181, 970422792, 949678364, 929394493, 909560097, 890164407, 871196953, 852647556, 834506317, 816763604, 799410050, 782436537, 765834191, 749594375, 733708678, 718168911, 702967096, 688095464, 673546445, 659312662, 645386927, 631762232, 618431749, 605388817, 592626943, 580139796, 567921199, 555965128, 544265708, 532817203, 521614021, 510650701, 499921915, 489422464, 479147270, 469091379, 459249952, 449618266, 440191708, 430965773, 421936063, 413098281, 404448229]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1141).prefactor = (5670080078977641/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1141).cutoff/(generalMeanRows 1141).c)).2 =
    (475379756884899/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1141).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1141).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1141).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1141

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1141).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1141).criticalRate j.val*(generalMeanRows 1141).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1141).c*(generalMeanRows 1141).criticalPoint j.val)).2-
      (generalMeanRows 1141).J/2-(generalMeanRows 1141).error (generalMeanGrid j.val)+
      (generalMeanRows 1141).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1141).c)).2-
      (generalMeanRows 1141).J/2-(generalMeanRows 1141).error 4 := by
  have he : (generalMeanRows 1141).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1141) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1141)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1141

/-! Kernel-checked entropy margins for general spectral rectangle 1142. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1142
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6610949297, 6413789603, 6224603494, 6042943852, 5868396097, 5700575268, 5539123435, 5383707368, 5234016461, 5089760857, 4950669758, 4816489901, 4686984180, 4561930392, 4441120100, 4324357600, 4211458973, 4102251230, 3996571518, 3894266400, 3795191198, 3699209376, 3606191992, 3516017175, 3428569658, 3343740336, 3261425868, 3181528298, 3103954716, 3028616934, 2955431191, 2884317883, 2815201302, 2748009402, 2682673579, 2619128468, 2557311749, 2497163971, 2438628386, 2381650798, 2326179412, 2272164706, 2219559302, 2168317849, 2118396913, 2069754872, 2022351823, 1976149491, 1931111140, 1887201498, 1844386681, 1802634121, 1761912503, 1722191701, 1683442719, 1645637641, 1608749571, 1572752592, 1537621716, 1503332843, 1469862718, 1437188894, 1405289695, 1374144181, 1343732119, 1314033947, 1285030748, 1256704223, 1229036664, 1202010928, 1175610417, 1149819052, 1124621254, 1100001925, 1075946426, 1052440563, 1029470565, 1007023072, 985085117, 963644113, 942687836, 922204417, 902182322, 882610347, 863477599, 844773494, 826487736, 808610317, 791131500, 774041811, 757332034, 740993200, 725016577, 709393665, 694116187, 679176083, 664565504, 650276801, 636302525, 622635415, 609268396, 596194573, 583407223, 570899793, 558665894, 546699294, 534993918, 523543838, 512343274, 501386586, 490668271, 480182961, 469925416, 459890525, 450073295, 440468858, 431072459, 421879455, 412885316, 404085617, 395476038]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1142).prefactor = (5889055764953539/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1142).cutoff/(generalMeanRows 1142).c)).2 =
    (235044369625241/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1142).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1142).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1142).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1142

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1142).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1142).criticalRate j.val*(generalMeanRows 1142).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1142).c*(generalMeanRows 1142).criticalPoint j.val)).2-
      (generalMeanRows 1142).J/2-(generalMeanRows 1142).error (generalMeanGrid j.val)+
      (generalMeanRows 1142).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1142).c)).2-
      (generalMeanRows 1142).J/2-(generalMeanRows 1142).error 4 := by
  have he : (generalMeanRows 1142).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1142) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1142)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1142

/-! Kernel-checked entropy margins for general spectral rectangle 1143. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1143
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7066825771, 6861297419, 6664005635, 6474487654, 6292314489, 6117087912, 5948437748, 5786019461, 5629511993, 5478615810, 5333051153, 5192556450, 5056886880, 4925813076, 4799119941, 4676605569, 4558080272, 4443365678, 4332293915, 4224706862, 4120455460, 4019399082, 3921404952, 3826347613, 3734108434, 3644575155, 3557641472, 3473206646, 3391175148, 3311456325, 3233964097, 3158616669, 3085336267, 3014048894, 2944684099, 2877174771, 2811456935, 2747469570, 2685154441, 2624455932, 2565320906, 2507698557, 2451540285, 2396799573, 2343431873, 2291394500, 2240646531, 2191148713, 2142863374, 2095754341, 2049786866, 2004927549, 1961144272, 1918406135, 1876683396, 1835947417, 1796170604, 1757326364, 1719389053, 1682333936, 1646137139, 1610775617, 1576227108, 1542470105, 1509483820, 1477248150, 1445743652, 1414951510, 1384853514, 1355432026, 1326669968, 1298550786, 1271058441, 1244177377, 1217892513, 1192189215, 1167053283, 1142470936, 1118428790, 1094913849, 1071913491, 1049415447, 1027407796, 1005878948, 984817636, 964212899, 944054077, 924330797, 905032966, 886150759, 867674609, 849595205, 831903476, 814590587, 797647931, 781067122, 764839987, 748958560, 733415075, 718201963, 703311840, 688737507, 674471942, 660508295, 646839884, 633460188, 620362844, 607541642, 594990522, 582703567, 570675002, 558899186, 547370614, 536083910, 525033820, 514215218, 503623093, 493252551, 483098811, 473157203, 463423162]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1143).prefactor = (6116488183529467/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1143).cutoff/(generalMeanRows 1143).c)).2 =
    (240349459181249/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1143).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1143).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1143).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1143

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1143).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1143).criticalRate j.val*(generalMeanRows 1143).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1143).c*(generalMeanRows 1143).criticalPoint j.val)).2-
      (generalMeanRows 1143).J/2-(generalMeanRows 1143).error (generalMeanGrid j.val)+
      (generalMeanRows 1143).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1143).c)).2-
      (generalMeanRows 1143).J/2-(generalMeanRows 1143).error 4 := by
  have he : (generalMeanRows 1143).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1143) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1143)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1143

/-! Kernel-checked entropy margins for general spectral rectangle 1144. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1144
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7665108919, 7450708837, 7244789185, 7046871694, 6856513177, 6673302385, 6496857196, 6326822100, 6162865949, 6004679929, 5851975735, 5704483919, 5561952404, 5424145124, 5290840800, 5161831817, 5036923208, 4915931723, 4798684973, 4685020659, 4574785849, 4467836329, 4364035997, 4263256307, 4165375765, 4070279447, 3977858577, 3888010113, 3800636384, 3715644745, 3632947254, 3552460382, 3474104735, 3397804803, 3323488721, 3251088051, 3180537576, 3111775110, 3044741322, 2979379568, 2915635739, 2853458116, 2792797235, 2733605762, 2675838376, 2619451655, 2564403981, 2510655436, 2458167714, 2406904039, 2356829082, 2307908888, 2260110806, 2213403424, 2167756505, 2123140932, 2079528650, 2036892617, 1995206755, 1954445905, 1914585780, 1875602933, 1837474708, 1800179213, 1763695281, 1728002441, 1693080882, 1658911431, 1625475522, 1592755172, 1560732953, 1529391975, 1498715857, 1468688714, 1439295130, 1410520144, 1382349231, 1354768285, 1327763601, 1301321866, 1275430136, 1250075829, 1225246708, 1200930872, 1177116740, 1153793041, 1130948807, 1108573357, 1086656290, 1065187475, 1044157042, 1023555375, 1003373101, 983601083, 964230413, 945252406, 926658590, 908440701, 890590679, 873100655, 855962955, 839170084, 822714728, 806589747, 790788168, 775303181, 760128136, 745256538, 730682039, 716398439, 702399681, 688679844, 675233142, 662053919, 649136647, 636475922, 624066460, 611903095, 599980774, 588294557, 576839613]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1144).prefactor = (6352703929532359/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1144).cutoff/(generalMeanRows 1144).c)).2 =
    (24841415014619/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1144).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1144).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1144).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1144

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1144).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1144).criticalRate j.val*(generalMeanRows 1144).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1144).c*(generalMeanRows 1144).criticalPoint j.val)).2-
      (generalMeanRows 1144).J/2-(generalMeanRows 1144).error (generalMeanGrid j.val)+
      (generalMeanRows 1144).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1144).c)).2-
      (generalMeanRows 1144).J/2-(generalMeanRows 1144).error 4 := by
  have he : (generalMeanRows 1144).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1144) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1144)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1144

/-! Kernel-checked entropy margins for general spectral rectangle 1145. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1145
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8190803008, 7970841080, 7759473923, 7556214475, 7360611587, 7172246787, 6990731403, 6815703984, 6646827996, 6483789737, 6326296469, 6174074731, 6026868803, 5884439323, 5746562029, 5613026607, 5483635652, 5358203713, 5236556417, 5118529675, 5003968951, 4892728587, 4784671187, 4679667052, 4577593652, 4478335148, 4381781947, 4287830288, 4196381864, 4107343471, 4020626680, 3936147539, 3853826288, 3773587104, 3695357854, 3619069877, 3544657769, 3472059193, 3401214696, 3332067539, 3264563545, 3198650943, 3134280240, 3071404089, 3009977167, 2949956067, 2891299192, 2833966655, 2777920191, 2723123067, 2669540003, 2617137099, 2565881757, 2515742623, 2466689517, 2418693378, 2371726209, 2325761023, 2280771794, 2236733414, 2193621646, 2151413083, 2110085113, 2069615881, 2029984251, 1991169780, 1953152682, 1915913802, 1879434588, 1843697065, 1808683810, 1774377931, 1740763041, 1707823242, 1675543101, 1643907635, 1612902292, 1582512931, 1552725812, 1523527576, 1494905233, 1466846148, 1439338025, 1412368900, 1385927126, 1360001359, 1334580555, 1309653950, 1285211060, 1261241664, 1237735798, 1214683748, 1192076039, 1169903431, 1148156906, 1126827665, 1105907122, 1085386895, 1065258798, 1045514840, 1026147217, 1007148303, 988510652, 970226985, 952290191, 934693319, 917429575, 900492317, 883875051, 867571428, 851575236, 835880402, 820480985, 805371173, 790545278, 775997738, 761723107, 747716057, 733971372, 720483948, 707248788]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1145).prefactor = (1624697486392061/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1145).cutoff/(generalMeanRows 1145).c)).2 =
    (513222110068057/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1145).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1145).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1145).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1145

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1145).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1145).criticalRate j.val*(generalMeanRows 1145).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1145).c*(generalMeanRows 1145).criticalPoint j.val)).2-
      (generalMeanRows 1145).J/2-(generalMeanRows 1145).error (generalMeanGrid j.val)+
      (generalMeanRows 1145).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1145).c)).2-
      (generalMeanRows 1145).J/2-(generalMeanRows 1145).error 4 := by
  have he : (generalMeanRows 1145).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1145) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1145)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1145

/-! Kernel-checked entropy margins for general spectral rectangle 1146. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1146
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5759610046, 5570826975, 5389998497, 5216675471, 5050441486, 4890909927, 4737721367, 4590541214, 4449057623, 4312979599, 4182035299, 4055970491, 3934547168, 3817542283, 3704746603, 3595963666, 3491008834, 3389708421, 3291898904, 3197426196, 3106144980, 3017918099, 2932615997, 2850116199, 2770302842, 2693066230, 2618302435, 2545912924, 2475804210, 2407887535, 2342078574, 2278297161, 2216467035, 2156515603, 2098373721, 2041975489, 1987258063, 1934161477, 1882628477, 1832604371, 1784036881, 1736876013, 1691073929, 1646584832, 1603364856, 1561371964, 1520565851, 1480907853, 1442360866, 1404889266, 1368458831, 1333036676, 1298591185, 1265091950, 1232509711, 1200816304, 1169984609, 1139988500, 1110802801, 1082403239, 1054766409, 1027869731, 1001691415, 976210428, 951406459, 927259887, 903751757, 880863747, 858578146, 836877823, 815746213, 795167283, 775125520, 755605906, 736593900, 718075419, 700036822, 682464891, 665346817, 648670185, 632422958, 616593464, 601170383, 586142735, 571499866, 557231439, 543327422, 529778075, 516573945, 503705852, 491164882, 478942378, 467029928, 455419363, 444102746, 433072361, 422320713, 411840515, 401624685, 391666337, 381958777, 372495494, 363270160, 354276617, 345508877, 336961116, 328627668, 320503020, 312581809, 304858816, 297328963, 289987307, 282829039, 275849478, 269044066, 262408367, 255938064, 249628952, 243476939, 237478039, 231628372]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1146).prefactor = (1177311783168809/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1146).cutoff/(generalMeanRows 1146).c)).2 =
    (457503360759309/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1146).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1146).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1146).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1146

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1146).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1146).criticalRate j.val*(generalMeanRows 1146).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1146).c*(generalMeanRows 1146).criticalPoint j.val)).2-
      (generalMeanRows 1146).J/2-(generalMeanRows 1146).error (generalMeanGrid j.val)+
      (generalMeanRows 1146).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1146).c)).2-
      (generalMeanRows 1146).J/2-(generalMeanRows 1146).error 4 := by
  have he : (generalMeanRows 1146).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1146) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1146)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1146

/-! Kernel-checked entropy margins for general spectral rectangle 1147. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1147
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5714268850, 5520764053, 5335541114, 5158132209, 4988103463, 4825051914, 4668602811, 4518407193, 4374139708, 4235496670, 4102194288, 3973967079, 3850566427, 3731759275, 3617326941, 3507064034, 3400777475, 3298285591, 3199417300, 3104011353, 3011915650, 2922986601, 2837088547, 2754093226, 2673879275, 2596331783, 2521341862, 2448806267, 2378627032, 2310711141, 2244970218, 2181320246, 2119681297, 2059977288, 2002135755, 1946087637, 1891767079, 1839111249, 1788060164, 1738556530, 1690545594, 1643975004, 1598794674, 1554956668, 1512415081, 1471125934, 1431047071, 1392138068, 1354360143, 1317676073, 1282050117, 1247447940, 1213836547, 1181184219, 1149460446, 1118635877, 1088682261, 1059572398, 1031280089, 1003780092, 977048079, 951060593, 925795014, 901229516, 877343041, 854115258, 831526538, 809557923, 788191094, 767408354, 747192593, 727527271, 708396391, 689784480, 671676569, 654058171, 636915264, 620234273, 604002054, 588205877, 572833410, 557872705, 543312185, 529140630, 515347163, 501921238, 488852632, 476131428, 463748008, 451693042, 439957477, 428532530, 417409678, 406580646, 396037403, 385772154, 375777328, 366045575, 356569757, 347342941, 338358393, 329609572, 321090124, 312793872, 304714819, 296847134, 289185151, 281723364, 274456419, 267379115, 260486394, 253773338, 247235167, 240867232, 234665014, 228624116, 222740266, 217009304, 211427189, 205989987, 200693874]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1147).prefactor = (1218644785503627/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1147).cutoff/(generalMeanRows 1147).c)).2 =
    (88552215804421/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1147).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1147).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1147).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1147

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1147).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1147).criticalRate j.val*(generalMeanRows 1147).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1147).c*(generalMeanRows 1147).criticalPoint j.val)).2-
      (generalMeanRows 1147).J/2-(generalMeanRows 1147).error (generalMeanGrid j.val)+
      (generalMeanRows 1147).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1147).c)).2-
      (generalMeanRows 1147).J/2-(generalMeanRows 1147).error 4 := by
  have he : (generalMeanRows 1147).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1147) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1147)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1147

/-! Kernel-checked entropy margins for general spectral rectangle 1148. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1148
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6637278391, 6443479938, 6257404178, 6078626164, 5906751323, 5741412763, 5582268862, 5429001117, 5281312217, 5138924306, 5001577420, 4869028076, 4741047999, 4617422953, 4497951697, 4382445021, 4270724871, 4162623550, 4057982987, 3956654067, 3858496012, 3763375819, 3671167735, 3581752783, 3495018312, 3410857595, 3329169446, 3249857870, 3172831744, 3098004509, 3025293897, 2954621667, 2885913367, 2819098108, 2754108354, 2690879729, 2629350837, 2569463086, 2511160537, 2454389751, 2399099653, 2345241400, 2292768262, 2241635508, 2191800298, 2143221585, 2095860020, 2049677862, 2004638901, 1960708373, 1917852893, 1876040383, 1835240007, 1795422111, 1756558166, 1718620714, 1681583314, 1645420499, 1610107723, 1575621328, 1541938493, 1509037204, 1476896212, 1445495004, 1414813763, 1384833347, 1355535252, 1326901586, 1298915048, 1271558896, 1244816927, 1218673457, 1193113294, 1168121725, 1143684491, 1119787769, 1096418161, 1073562671, 1051208691, 1029343988, 1007956689, 987035265, 966568524, 946545590, 926955901, 907789190, 889035479, 870685067, 852728521, 835156663, 817960570, 801131556, 784661167, 768541177, 752763576, 737320564, 722204545, 707408119, 692924078, 678745397, 664865232, 651276911, 637973928, 624949944, 612198773, 599714386, 587490900, 575522577, 563803819, 552329164, 541093281, 530090968, 519317147, 508766861, 498435269, 488317647, 478409382, 468705965, 459202997, 449896179, 440781312]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1148).prefactor = (5582582985475257/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1148).cutoff/(generalMeanRows 1148).c)).2 =
    (437472590762467/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1148).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1148).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1148).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1148

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1148).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1148).criticalRate j.val*(generalMeanRows 1148).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1148).c*(generalMeanRows 1148).criticalPoint j.val)).2-
      (generalMeanRows 1148).J/2-(generalMeanRows 1148).error (generalMeanGrid j.val)+
      (generalMeanRows 1148).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1148).c)).2-
      (generalMeanRows 1148).J/2-(generalMeanRows 1148).error 4 := by
  have he : (generalMeanRows 1148).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1148) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1148)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1148

/-! Kernel-checked entropy margins for general spectral rectangle 1149. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1149
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6687477093, 6484794993, 6290297526, 6103535495, 5924091668, 5751577939, 5585632810, 5425919122, 5272122035, 5123947204, 4981119135, 4843379709, 4710486830, 4582213215, 4458345284, 4338682152, 4223034708, 4111224776, 4003084345, 3898454864, 3797186597, 3699138021, 3604175286, 3512171705, 3423007290, 3336568322, 3252746951, 3171440829, 3092552767, 3015990422, 2941665996, 2869495972, 2799400849, 2731304914, 2665136019, 2600825371, 2538307349, 2477519316, 2418401457, 2360896623, 2304950180, 2250509877, 2197525716, 2145949831, 2095736375, 2046841415, 1999222835, 1952840238, 1907654861, 1863629493, 1820728397, 1778917234, 1738163001, 1698433958, 1659699575, 1621930466, 1585098344, 1549175962, 1514137066, 1479956355, 1446609431, 1414072758, 1382323632, 1351340132, 1321101096, 1291586081, 1262775337, 1234649773, 1207190934, 1180380968, 1154202608, 1128639142, 1103674395, 1079292705, 1055478900, 1032218285, 1009496617, 987300093, 965615327, 944429339, 923729538, 903503706, 883739986, 864426871, 845553183, 827108072, 809080995, 791461712, 774240270, 757406997, 740952489, 724867604, 709143451, 693771383, 678742987, 664050078, 649684690, 635639071, 621905674, 608477152, 595346351, 582506302, 569950221, 557671495, 545663685, 533920514, 522435867, 511203783, 500218453, 489474212, 478965537, 468687046, 458633486, 448799737, 439180804, 429771815, 420568017, 411564772, 402757556, 394141952, 385713653]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1149).prefactor = (9173464940039/1562500000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1149).cutoff/(generalMeanRows 1149).c)).2 =
    (21062800958661/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1149).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1149).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1149).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1149

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1149).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1149).criticalRate j.val*(generalMeanRows 1149).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1149).c*(generalMeanRows 1149).criticalPoint j.val)).2-
      (generalMeanRows 1149).J/2-(generalMeanRows 1149).error (generalMeanGrid j.val)+
      (generalMeanRows 1149).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1149).c)).2-
      (generalMeanRows 1149).J/2-(generalMeanRows 1149).error 4 := by
  have he : (generalMeanRows 1149).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1149) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1149)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1149

/-! Kernel-checked entropy margins for general spectral rectangle 1150. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1150
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6345975021, 6163189400, 5987675590, 5819028184, 5656871174, 5500855327, 5350655842, 5205970250, 5066516539, 4932031459, 4802269005, 4676999038, 4556006040, 4439087988, 4326055324, 4216730026, 4110944754, 4008542070, 3909373732, 3813300040, 3720189238, 3629916966, 3542365757, 3457424567, 3374988354, 3294957677, 3217238337, 3141741031, 3068381048, 2997077976, 2927755433, 2860340820, 2794765090, 2730962532, 2668870571, 2608429582, 2549582721, 2492275756, 2436456924, 2382076784, 2329088092, 2277445674, 2227106311, 2178028637, 2130173033, 2083501535, 2037977746, 1993566755, 1950235056, 1907950479, 1866682118, 1826400272, 1787076377, 1748682959, 1711193573, 1674582754, 1638825974, 1603899592, 1569780816, 1536447662, 1503878916, 1472054099, 1440953435, 1410557818, 1380848781, 1351808474, 1323419629, 1295665540, 1268530040, 1241997473, 1216052679, 1190680969, 1165868108, 1141600296, 1117864152, 1094646695, 1071935331, 1049717834, 1027982338, 1006717319, 985911583, 965554254, 945634763, 926142837, 907068486, 888401995, 870133917, 852255058, 834756471, 817629449, 800865515, 784456416, 768394112, 752670775, 737278776, 722210682, 707459251, 693017422, 678878312, 665035210, 651481573, 638211018, 625217320, 612494406, 600036350, 587837370, 575891823, 564194202, 552739130, 541521359, 530535763, 519777340, 509241203, 498922578, 488816804, 478919328, 469225701, 459731576, 450432707, 441324945, 432404232]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1150).prefactor = (2685870754734991/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1150).cutoff/(generalMeanRows 1150).c)).2 =
    (470046183342651/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1150).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1150).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1150).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1150

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1150).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1150).criticalRate j.val*(generalMeanRows 1150).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1150).c*(generalMeanRows 1150).criticalPoint j.val)).2-
      (generalMeanRows 1150).J/2-(generalMeanRows 1150).error (generalMeanGrid j.val)+
      (generalMeanRows 1150).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1150).c)).2-
      (generalMeanRows 1150).J/2-(generalMeanRows 1150).error 4 := by
  have he : (generalMeanRows 1150).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1150) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1150)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1150

/-! Kernel-checked entropy margins for general spectral rectangle 1151. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1151
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6539212835, 6348450641, 6165311206, 5989370019, 5820233306, 5657535288, 5500935726, 5350117739, 5204785833, 5064664141, 4929494829, 4799036660, 4673063693, 4551364103, 4433739110, 4320002003, 4209977250, 4103499685, 4000413765, 3900572891, 3803838780, 3710080895, 3619175915, 3531007250, 3445464595, 3362443513, 3281845059, 3203575420, 3127545597, 3053671094, 2981871643, 2912070943, 2844196415, 2778178983, 2713952859, 2651455351, 2590626683, 2531409825, 2473750336, 2417596214, 2362897764, 2309607464, 2257679849, 2207071397, 2157740424, 2109646987, 2062752788, 2017021093, 1972416644, 1928905590, 1886455409, 1845034846, 1804613847, 1765163499, 1726655975, 1689064482, 1652363211, 1616527290, 1581532739, 1547356430, 1513976047, 1481370048, 1449517634, 1418398709, 1387993855, 1358284301, 1329251892, 1300879066, 1273148827, 1246044723, 1219550820, 1193651686, 1168332365, 1143578362, 1119375622, 1095710516, 1072569819, 1049940700, 1027810703, 1006167738, 985000059, 964296259, 944045254, 924236273, 904858844, 885902787, 867358201, 849215455, 831465181, 814098260, 797105819, 780479221, 764210054, 748290128, 732711467, 717466300, 702547055, 687946356, 673657011, 659672014, 645984531, 632587901, 619475627, 606641374, 594078962, 581782363, 569745696, 557963221, 546429338, 535138581, 524085616, 513265235, 502672354, 492302008, 482149351, 472209650, 462478281, 452950730, 443622586, 434489542, 425547389]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1151).prefactor = (2807643607896293/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1151).cutoff/(generalMeanRows 1151).c)).2 =
    (232349288508029/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1151).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1151).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1151).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1151

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1151).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1151).criticalRate j.val*(generalMeanRows 1151).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1151).c*(generalMeanRows 1151).criticalPoint j.val)).2-
      (generalMeanRows 1151).J/2-(generalMeanRows 1151).error (generalMeanGrid j.val)+
      (generalMeanRows 1151).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1151).c)).2-
      (generalMeanRows 1151).J/2-(generalMeanRows 1151).error 4 := by
  have he : (generalMeanRows 1151).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1151) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1151)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1151

/-! Kernel-checked entropy margins for general spectral rectangle 1152. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1152
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6642882490, 6444207791, 6253544313, 6070446737, 5894501883, 5725325849, 5562561449, 5405875931, 5254958924, 5109520594, 4969289982, 4834013505, 4703453595, 4577387468, 4455606003, 4337912724, 4224122871, 4114062547, 4007567944, 3904484634, 3804666911, 3707977194, 3614285476, 3523468816, 3435410870, 3350001458, 3267136169, 3186715986, 3108646949, 3032839837, 2959209872, 2887676452, 2818162891, 2750596190, 2684906815, 2621028490, 2558898016, 2498455084, 2439642117, 2382404112, 2326688497, 2272444998, 2219625510, 2168183980, 2118076300, 2069260197, 2021695144, 1975342262, 1930164238, 1886125246, 1843190868, 1801328029, 1760504922, 1720690955, 1681856684, 1643973764, 1607014890, 1570953754, 1535764995, 1501424156, 1467907643, 1435192683, 1403257294, 1372080241, 1341641010, 1311919774, 1282897362, 1254555234, 1226875454, 1199840661, 1173434050, 1147639347, 1122440787, 1097823097, 1073771469, 1050271552, 1027309425, 1004871587, 982944937, 961516760, 940574714, 920106815, 900101424, 880547234, 861433260, 842748826, 824483553, 806627353, 789170413, 772103191, 755416403, 739101019, 723148248, 707549536, 692296555, 677381198, 662795568, 648531976, 634582934, 620941144, 607599497, 594551065, 581789098, 569307014, 557098399, 545156997, 533476711, 522051595, 510875847, 499943813, 489249972, 478788943, 468555473, 458544437, 448750835, 439169786, 429796526, 420626406, 411654888, 402877541, 394290038]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1152).prefactor = (2934937436979801/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1152).cutoff/(generalMeanRows 1152).c)).2 =
    (454088397904041/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1152).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1152).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1152).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1152

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1152).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1152).criticalRate j.val*(generalMeanRows 1152).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1152).c*(generalMeanRows 1152).criticalPoint j.val)).2-
      (generalMeanRows 1152).J/2-(generalMeanRows 1152).error (generalMeanGrid j.val)+
      (generalMeanRows 1152).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1152).c)).2-
      (generalMeanRows 1152).J/2-(generalMeanRows 1152).error 4 := by
  have he : (generalMeanRows 1152).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1152) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1152)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1152

/-! Kernel-checked entropy margins for general spectral rectangle 1153. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1153
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6325521752, 6145217456, 5972065781, 5805663191, 5645635874, 5491637066, 5343344662, 5200459078, 5062701339, 4929811350, 4801546350, 4677679510, 4557998661, 4442305152, 4330412801, 4222146947, 4117343585, 4015848580, 3917516941, 3822212163, 3729805624, 3640176026, 3553208890, 3468796084, 3386835391, 3307230115, 3229888713, 3154724451, 3081655100, 3010602640, 2941492993, 2874255777, 2808824073, 2745134214, 2683125584, 2622740435, 2563923715, 2506622909, 2450787890, 2396370781, 2343325825, 2291609266, 2241179233, 2191995642, 2144020091, 2097215770, 2051547378, 2006981040, 1963484233, 1921025712, 1879575449, 1839104570, 1799585292, 1760990875, 1723295564, 1686474547, 1650503904, 1615360570, 1581022288, 1547467578, 1514675695, 1482626600, 1451300925, 1420679947, 1390745554, 1361480224, 1332866995, 1304889444, 1277531664, 1250778240, 1224614234, 1199025159, 1173996966, 1149516025, 1125569108, 1102143374, 1079226354, 1056805937, 1034870356, 1013408177, 992408285, 971859873, 951752432, 932075737, 912819844, 893975072, 875531999, 857481454, 839814504, 822522452, 805596823, 789029362, 772812025, 756936971, 741396559, 726183337, 711290040, 696709585, 682435059, 668459724, 654777003, 641380479, 628263890, 615421126, 602846221, 590533353, 578476836, 566671119, 555110782, 543790532, 532705198, 521849730, 511219196, 500808774, 490613758, 480629544, 470851638, 461275646, 451897273, 442712321, 433716689]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1153).prefactor = (2704125305523611/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1153).cutoff/(generalMeanRows 1153).c)).2 =
    (100549328930717/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1153).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1153).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1153).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1153

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1153).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1153).criticalRate j.val*(generalMeanRows 1153).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1153).c*(generalMeanRows 1153).criticalPoint j.val)).2-
      (generalMeanRows 1153).J/2-(generalMeanRows 1153).error (generalMeanGrid j.val)+
      (generalMeanRows 1153).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1153).c)).2-
      (generalMeanRows 1153).J/2-(generalMeanRows 1153).error 4 := by
  have he : (generalMeanRows 1153).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1153) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1153)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1153

/-! Kernel-checked entropy margins for general spectral rectangle 1154. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1154
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6487298790, 6300012571, 6120189746, 5947409734, 5781282882, 5621447683, 5467568287, 5319332287, 5176448719, 5038646278, 4905671700, 4777288305, 4653274684, 4533423496, 4417540389, 4305443010, 4196960107, 4091930706, 3990203362, 3891635475, 3796092654, 3703448148, 3613582310, 3526382112, 3441740693, 3359556951, 3279735154, 3202184594, 3126819257, 3053557524, 2982321891, 2913038709, 2845637948, 2780052972, 2716220331, 2654079572, 2593573059, 2534645807, 2477245326, 2421321479, 2366826344, 2313714094, 2261940874, 2211464696, 2162245332, 2114244223, 2067424387, 2021750338, 1977188000, 1933704644, 1891268810, 1849850247, 1809419852, 1769949609, 1731412541, 1693782655, 1657034897, 1621145107, 1586089975, 1551847004, 1518394471, 1485711393, 1453777492, 1422573165, 1392079453, 1362278016, 1333151102, 1304681526, 1276852644, 1249648331, 1223052960, 1197051382, 1171628905, 1146771281, 1122464681, 1098695685, 1075451264, 1052718764, 1030485896, 1008740719, 987471626, 966667336, 946316882, 926409596, 906935101, 887883302, 869244376, 851008759, 833167144, 815710466, 798629899, 781916845, 765562927, 749559986, 733900068, 718575421, 703578490, 688901907, 674538490, 660481233, 646723304, 633258038, 620078934, 607179647, 594553987, 582195914, 570099531, 558259083, 546668950, 535323649, 524217822, 513346241, 502703798, 492285504, 482086488, 472101990, 462327363, 452758063, 443389653, 434217798, 425238260]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1154).prefactor = (5626720389793733/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1154).cutoff/(generalMeanRows 1154).c)).2 =
    (497497288767443/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1154).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1154).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1154).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1154

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1154).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1154).criticalRate j.val*(generalMeanRows 1154).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1154).c*(generalMeanRows 1154).criticalPoint j.val)).2-
      (generalMeanRows 1154).J/2-(generalMeanRows 1154).error (generalMeanGrid j.val)+
      (generalMeanRows 1154).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1154).c)).2-
      (generalMeanRows 1154).J/2-(generalMeanRows 1154).error 4 := by
  have he : (generalMeanRows 1154).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1154) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1154)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1154

/-! Kernel-checked entropy margins for general spectral rectangle 1155. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1155
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6653363550, 6458854083, 6272131699, 6092758038, 5920326919, 5754461449, 5594811439, 5441051096, 5292876948, 5150005987, 5012173985, 4879133982, 4750654917, 4626520379, 4506527488, 4390485857, 4278216665, 4169551800, 4064333078, 3962411529, 3863646744, 3767906274, 3675065076, 3585005008, 3497614362, 3412787432, 3330424116, 3250429554, 3172713781, 3097191421, 3023781392, 2952406638, 2882993879, 2815473381, 2749778739, 2685846676, 2623616860, 2563031729, 2504036330, 2446578168, 2390607067, 2336075038, 2282936158, 2231146454, 2180663801, 2131447814, 2083459763, 2036662480, 1991020280, 1946498883, 1903065342, 1860687975, 1819336303, 1778980988, 1739593780, 1701147460, 1663615797, 1626973493, 1591196145, 1556260203, 1522142927, 1488822357, 1456277269, 1424487151, 1393432166, 1363093126, 1333451464, 1304489204, 1276188941, 1248533815, 1221507489, 1195094129, 1169278379, 1144045352, 1119380600, 1095270107, 1071700265, 1048657863, 1026130071, 1004104426, 982568819, 961511479, 940920968, 920786161, 901096241, 881840685, 863009256, 844591992, 826579199, 808961438, 791729520, 774874497, 758387655, 742260505, 726484775, 711052408, 695955549, 681186545, 666737933, 652602439, 638772969, 625242606, 612004605, 599052384, 586379525, 573979764, 561846992, 549975245, 538358703, 526991688, 515868655, 504984193, 494333018, 483909971, 473710015, 463728233, 453959821, 444400087, 435044450, 425888434, 416927668]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1155).prefactor = (5854015396448141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1155).cutoff/(generalMeanRows 1155).c)).2 =
    (492275344786291/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1155).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1155).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1155).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1155

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1155).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1155).criticalRate j.val*(generalMeanRows 1155).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1155).c*(generalMeanRows 1155).criticalPoint j.val)).2-
      (generalMeanRows 1155).J/2-(generalMeanRows 1155).error (generalMeanGrid j.val)+
      (generalMeanRows 1155).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1155).c)).2-
      (generalMeanRows 1155).J/2-(generalMeanRows 1155).error 4 := by
  have he : (generalMeanRows 1155).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1155) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1155)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1155

/-! Kernel-checked entropy margins for general spectral rectangle 1156. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1156
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6727085986, 6525516500, 6332093188, 6146358279, 5967887503, 5796287072, 5631191007, 5472258726, 5319172901, 5171637515, 5029376122, 4892130271, 4759658078, 4631732938, 4508142348, 4388686842, 4273179015, 4161442639, 4053311846, 3948630390, 3847250961, 3749034567, 3653849952, 3561573074, 3472086616, 3385279535, 3301046657, 3219288285, 3139909851, 3062821589, 2987938232, 2915178730, 2844465992, 2775726643, 2708890799, 2643891860, 2580666316, 2519153563, 2459295740, 2401037568, 2344326202, 2289111102, 2235343896, 2182978266, 2131969838, 2082276072, 2033856170, 1986670978, 1940682908, 1895855852, 1852155108, 1809547310, 1768000359, 1727483364, 1687966580, 1649421355, 1611820076, 1575136121, 1539343813, 1504418376, 1470335893, 1437073270, 1404608194, 1372919106, 1341985162, 1311786204, 1282302732, 1253515874, 1225407363, 1197959509, 1171155176, 1144977761, 1119411173, 1094439810, 1070048544, 1046222698, 1022948034, 1000210732, 977997376, 956294942, 935090778, 914372594, 894128450, 874346742, 855016189, 836125826, 817664986, 799623300, 781990676, 764757299, 747913616, 731450330, 715358390, 699628987, 684253540, 669223695, 654531315, 640168471, 626127442, 612400703, 598980920, 585860946, 573033816, 560492739, 548231094, 536242427, 524520442, 513059000, 501852116, 490893948, 480178800, 469701114, 459455468, 449436571, 439639261, 430058499, 420689367, 411527068, 402566915, 393804337, 385234870]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1156).prefactor = (6090492131795469/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1156).cutoff/(generalMeanRows 1156).c)).2 =
    (481912557750743/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1156).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1156).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1156).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1156

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1156).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1156).criticalRate j.val*(generalMeanRows 1156).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1156).c*(generalMeanRows 1156).criticalPoint j.val)).2-
      (generalMeanRows 1156).J/2-(generalMeanRows 1156).error (generalMeanGrid j.val)+
      (generalMeanRows 1156).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1156).c)).2-
      (generalMeanRows 1156).J/2-(generalMeanRows 1156).error 4 := by
  have he : (generalMeanRows 1156).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1156) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1156)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1156

/-! Kernel-checked entropy margins for general spectral rectangle 1157. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1157
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6899759302, 6690504291, 6489746789, 6297009629, 6111850499, 5933858821, 5762652953, 5597877697, 5439202060, 5286317239, 5138934804, 4996785069, 4859615599, 4727189874, 4599286062, 4475695915, 4356223751, 4240685532, 4128908020, 4020728004, 3915991592, 3814553558, 3716276747, 3621031525, 3528695273, 3439151919, 3352291510, 3268009810, 3186207938, 3106792022, 3029672888, 2954765767, 2881990021, 2811268896, 2742529284, 2675701508, 2610719120, 2547518711, 2486039737, 2426224354, 2368017266, 2311365584, 2256218689, 2202528113, 2150247417, 2099332086, 2049739426, 2001428468, 1954359877, 1908495873, 1863800147, 1820237788, 1777775216, 1736380114, 1696021368, 1656669008, 1618294156, 1580868969, 1544366600, 1508761142, 1474027593, 1440141812, 1407080480, 1374821066, 1343341790, 1312621594, 1282640109, 1253377627, 1224815070, 1196933972, 1169716446, 1143145164, 1117203336, 1091874686, 1067143434, 1042994277, 1019412369, 996383305, 973893106, 951928200, 930475409, 909521935, 889055347, 869063565, 849534852, 830457797, 811821310, 793614604, 775827192, 758448871, 741469717, 724880072, 708670538, 692831969, 677355461, 662232345, 647454180, 633012747, 618900039, 605108259, 591629808, 578457285, 565583478, 553001356, 540704069, 528684940, 516937458, 505455278, 494232212, 483262225, 472539434, 462058101, 451812629, 441797557, 432007560, 422437444, 413082138, 403936698, 394996296, 386256225, 377711887]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1157).prefactor = (1584130374425089/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1157).cutoff/(generalMeanRows 1157).c)).2 =
    (119192789562581/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1157).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1157).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1157).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1157

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1157).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1157).criticalRate j.val*(generalMeanRows 1157).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1157).c*(generalMeanRows 1157).criticalPoint j.val)).2-
      (generalMeanRows 1157).J/2-(generalMeanRows 1157).error (generalMeanGrid j.val)+
      (generalMeanRows 1157).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1157).c)).2-
      (generalMeanRows 1157).J/2-(generalMeanRows 1157).error 4 := by
  have he : (generalMeanRows 1157).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1157) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1157)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1157

/-! Kernel-checked entropy margins for general spectral rectangle 1158. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1158
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7386275420, 7167645442, 6957809279, 6756272359, 6562576360, 6376295950, 6197035878, 6024428380, 5858130841, 5697823702, 5543208573, 5394006521, 5249956535, 5110814120, 4976350032, 4846349117, 4720609259, 4598940423, 4481163768, 4367110852, 4256622887, 4149550067, 4045750946, 3945091866, 3847446430, 3752695020, 3660724346, 3571427033, 3484701241, 3400450310, 3318582435, 3239010357, 3161651089, 3086425649, 3013258819, 2942078922, 2872817609, 2805409665, 2739792826, 2675907611, 2613697164, 2553107103, 2494085388, 2436582186, 2380549754, 2325942326, 2272716008, 2220828677, 2170239891, 2120910800, 2072804065, 2025883786, 1980115421, 1935465728, 1891902697, 1849395490, 1807914385, 1767430727, 1727916871, 1689346144, 1651692793, 1614931947, 1579039577, 1543992458, 1509768135, 1476344891, 1443701710, 1411818254, 1380674830, 1350252367, 1320532387, 1291496984, 1263128799, 1235411000, 1208327261, 1181861741, 1155999068, 1130724320, 1106023009, 1081881063, 1058284811, 1035220973, 1012676641, 990639265, 969096648, 948036925, 927448557, 907320317, 887641282, 868400822, 849588589, 831194510, 813208777, 795621839, 778424391, 761607372, 745161952, 729079528, 713351716, 697970345, 682927448, 668215262, 653826213, 639752920, 625988182, 612524977, 599356455, 586475933, 573876893, 561552974, 549497968, 537705819, 526170614, 514886584, 503848096, 493049653, 482485887, 472151557, 462041545, 452150857, 442474612]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1158).prefactor = (824061172355997/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1158).cutoff/(generalMeanRows 1158).c)).2 =
    (243540263954593/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1158).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1158).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1158).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1158

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1158).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1158).criticalRate j.val*(generalMeanRows 1158).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1158).c*(generalMeanRows 1158).criticalPoint j.val)).2-
      (generalMeanRows 1158).J/2-(generalMeanRows 1158).error (generalMeanGrid j.val)+
      (generalMeanRows 1158).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1158).c)).2-
      (generalMeanRows 1158).J/2-(generalMeanRows 1158).error 4 := by
  have he : (generalMeanRows 1158).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1158) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1158)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1158

/-! Kernel-checked entropy margins for general spectral rectangle 1159. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1159
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8126421757, 7900731261, 7683915094, 7475471248, 7274934822, 7081874672, 6895890424, 6716609808, 6543686259, 6376796769, 6215639941, 6059934246, 5909416432, 5763840094, 5622974365, 5486602733, 5354521962, 5226541102, 5102480590, 4982171428, 4865454424, 4752179500, 4642205059, 4535397395, 4431630156, 4330783850, 4232745385, 4137407647, 4044669107, 3954433465, 3866609313, 3781109823, 3697852464, 3616758733, 3537753908, 3460766820, 3385729637, 3312577667, 3241249172, 3171685195, 3103829403, 3037627930, 2973029247, 2909984021, 2848445002, 2788366902, 2729706293, 2672421504, 2616472532, 2561820947, 2508429819, 2456263634, 2405288223, 2355470699, 2306779385, 2259183764, 2212654414, 2167162961, 2122682024, 2079185174, 2036646886, 1995042498, 1954348172, 1914540857, 1875598254, 1837498783, 1800221552, 1763746326, 1728053503, 1693124083, 1658939645, 1625482325, 1592734791, 1560680221, 1529302288, 1498585134, 1468513357, 1439071993, 1410246495, 1382022724, 1354386930, 1327325739, 1300826139, 1274875469, 1249461402, 1224571941, 1200195401, 1176320400, 1152935853, 1130030955, 1107595180, 1085618264, 1064090202, 1043001239, 1022341861, 1002102786, 982274960, 962849550, 943817935, 925171701, 906902634, 889002717, 871464121, 854279200, 837440487, 820940691, 804772686, 788929513, 773404372, 758190617, 743281754, 728671436, 714353458, 700321758, 686570404, 673093601, 659885681, 646941101, 634254441, 621820400, 609633792]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1159).prefactor = (6751006940367103/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1159).cutoff/(generalMeanRows 1159).c)).2 =
    (128332188496031/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1159).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1159).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1159).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1159

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1159).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1159).criticalRate j.val*(generalMeanRows 1159).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1159).c*(generalMeanRows 1159).criticalPoint j.val)).2-
      (generalMeanRows 1159).J/2-(generalMeanRows 1159).error (generalMeanGrid j.val)+
      (generalMeanRows 1159).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1159).c)).2-
      (generalMeanRows 1159).J/2-(generalMeanRows 1159).error 4 := by
  have he : (generalMeanRows 1159).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1159) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1159)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1159

/-! Kernel-checked entropy margins for general spectral rectangle 1160. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1160
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5950846350, 5758885474, 5574933691, 5398537791, 5229277882, 5066764387, 4910635361, 4760554094, 4616206957, 4477301473, 4343564571, 4214741015, 4090591984, 3970893776, 3855436646, 3744023737, 3636470111, 3532601867, 3432255334, 3335276329, 3241519484, 3150847625, 3063131204, 2978247772, 2896081502, 2816522744, 2739467616, 2664817625, 2592479324, 2522363985, 2454387303, 2388469118, 2324533163, 2262506825, 2202320922, 2143909502, 2087209652, 2032161319, 1978707149, 1926792330, 1876364449, 1827373362, 1779771064, 1733511577, 1688550840, 1644846606, 1602358348, 1561047168, 1520875715, 1481808106, 1443809853, 1406847792, 1370890021, 1335905837, 1301865677, 1268741067, 1236504573, 1205129744, 1174591079, 1144863975, 1115924689, 1087750305, 1060318689, 1033608466, 1007598976, 982270254, 957602995, 933578529, 910178793, 887386311, 865184165, 843555976, 822485885, 801958527, 781959018, 762472934, 743486292, 724985539, 706957531, 689389519, 672269137, 655584389, 639323631, 623475563, 608029216, 592973939, 578299392, 563995530, 550052599, 536461121, 523211888, 510295954, 497704623, 485429443, 473462199, 461794905, 450419794, 439329316, 428516127, 417973085, 407693244, 397669844, 387896313, 378366253, 369073440, 360011819, 351175494, 342558731, 334155944, 325961700, 317970708, 310177817, 302578014, 295166415, 287938268, 280888943, 274013932, 267308846, 260769408, 254391455, 248170931]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1160).prefactor = (150736994121601/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1160).cutoff/(generalMeanRows 1160).c)).2 =
    (480827958945943/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1160).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1160).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1160).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1160

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1160).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1160).criticalRate j.val*(generalMeanRows 1160).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1160).c*(generalMeanRows 1160).criticalPoint j.val)).2-
      (generalMeanRows 1160).J/2-(generalMeanRows 1160).error (generalMeanGrid j.val)+
      (generalMeanRows 1160).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1160).c)).2-
      (generalMeanRows 1160).J/2-(generalMeanRows 1160).error 4 := by
  have he : (generalMeanRows 1160).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1160) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1160)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1160

/-! Kernel-checked entropy margins for general spectral rectangle 1161. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1161
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5912155642, 5715099662, 5526396112, 5345572251, 5172189937, 5005842518, 4846152051, 4692766824, 4545359121, 4403623223, 4267273604, 4136043296, 4009682419, 3887956845, 3770646982, 3657546670, 3548462179, 3443211290, 3341622456, 3243534038, 3148793601, 3057257270, 2968789139, 2883260730, 2800550488, 2720543323, 2643130183, 2568207665, 2495677649, 2425446964, 2357427079, 2291533811, 2227687064, 2165810580, 2105831705, 2047681182, 1991292947, 1936603947, 1883553968, 1832085473, 1782143452, 1733675286, 1686630611, 1640961200, 1596620848, 1553565263, 1511751971, 1471140217, 1431690879, 1393366388, 1356130648, 1319948962, 1284787968, 1250615571, 1217400885, 1185114173, 1153726798, 1123211166, 1093540686, 1064689719, 1036633536, 1009348283, 982810934, 956999266, 931891815, 907467850, 883707340, 860590926, 838099891, 816216140, 794922167, 774201038, 754036367, 734412292, 715313458, 696724997, 678632507, 661022040, 643880078, 627193525, 610949685, 595136251, 579741290, 564753231, 550160852, 535953265, 522119908, 508650532, 495535192, 482764234, 470328287, 458218255, 446425304, 434940857, 423756585, 412864395, 402256430, 391925054, 381862849, 372062608, 362517326, 353220197, 344164604, 335344118, 326752488, 318383636, 310231654, 302290799, 294555484, 287020277, 279679897, 272529205, 265563206, 258777039, 252165976, 245725419, 239450894, 233338047, 227382645, 221580566, 215927801]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1161).prefactor = (3124379102950083/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1161).cutoff/(generalMeanRows 1161).c)).2 =
    (46629985838303/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1161).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1161).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1161).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1161

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1161).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1161).criticalRate j.val*(generalMeanRows 1161).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1161).c*(generalMeanRows 1161).criticalPoint j.val)).2-
      (generalMeanRows 1161).J/2-(generalMeanRows 1161).error (generalMeanGrid j.val)+
      (generalMeanRows 1161).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1161).c)).2-
      (generalMeanRows 1161).J/2-(generalMeanRows 1161).error 4 := by
  have he : (generalMeanRows 1161).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1161) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1161)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1161

/-! Kernel-checked entropy margins for general spectral rectangle 1162. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1162
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6367701250, 6164574804, 5969879319, 5783137659, 5603907814, 5431779740, 5266372522, 5107331844, 4954327724, 4807052466, 4665218827, 4528558357, 4396819897, 4269768220, 4147182794, 4028856665, 3914595427, 3804216296, 3697547258, 3594426286, 3494700631, 3398226165, 3304866784, 3214493855, 3126985707, 3042227167, 2960109127, 2880528146, 2803386084, 2728589764, 2656050657, 2585684588, 2517411473, 2451155064, 2386842720, 2324405187, 2263776407, 2204893321, 2147695701, 2092125992, 2038129152, 1985652520, 1934645682, 1885060346, 1836850233, 1789970964, 1744379965, 1700036368, 1656900930, 1614935943, 1574105161, 1534373728, 1495708108, 1458076021, 1421446383, 1385789251, 1351075766, 1317278107, 1284369440, 1252323876, 1221116427, 1190722967, 1161120192, 1132285591, 1104197405, 1076834598, 1050176827, 1024204415, 998898320, 974240114, 950211953, 926796559, 903977197, 881737650, 860062205, 838935630, 818343156, 798270463, 778703660, 759629272, 741034223, 722905824, 705231758, 688000065, 671199135, 654817691, 638844780, 623269761, 608082295, 593272337, 578830122, 564746161, 551011227, 537616350, 524552809, 511812121, 499386038, 487266534, 475445804, 463916254, 452670495, 441701337, 431001782, 420565020, 410384423, 400453540, 390766087, 381315952, 372097179, 363103972, 354330685, 345771820, 337422024, 329276081, 321328913, 313575572, 306011238, 298631217, 291430933, 284405931, 277551867]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1162).prefactor = (6361370039443201/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1162).cutoff/(generalMeanRows 1162).c)).2 =
    (121429486060033/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1162).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1162).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1162).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1162

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1162).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1162).criticalRate j.val*(generalMeanRows 1162).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1162).c*(generalMeanRows 1162).criticalPoint j.val)).2-
      (generalMeanRows 1162).J/2-(generalMeanRows 1162).error (generalMeanGrid j.val)+
      (generalMeanRows 1162).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1162).c)).2-
      (generalMeanRows 1162).J/2-(generalMeanRows 1162).error 4 := by
  have he : (generalMeanRows 1162).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1162) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1162)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1162

/-! Kernel-checked entropy margins for general spectral rectangle 1163. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1163
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6436287917, 6254553038, 6079981054, 5912170690, 5750750034, 5595373906, 5445721501, 5301494284, 5162414108, 5028221510, 4898674192, 4773545635, 4652623851, 4535710253, 4422618627, 4313174194, 4207212761, 4104579938, 4005130432, 3908727392, 3815241812, 3724551987, 3636543003, 3551106281, 3468139142, 3387544421, 3309230101, 3233108975, 3159098340, 3087119706, 3017098535, 2948963988, 2882648700, 2818088569, 2755222553, 2693992493, 2634342937, 2576220985, 2519576135, 2464360151, 2410526932, 2358032389, 2306834336, 2256892382, 2208167835, 2160623609, 2114224137, 2068935294, 2024724317, 1981559733, 1939411301, 1898249939, 1858047672, 1818777577, 1780413725, 1742931140, 1706305750, 1670514340, 1635534519, 1601344675, 1567923943, 1535252169, 1503309876, 1472078240, 1441539054, 1411674704, 1382468147, 1353902879, 1325962918, 1298632780, 1271897461, 1245742412, 1220153526, 1195117118, 1170619908, 1146649007, 1123191901, 1100236433, 1077770798, 1055783521, 1034263451, 1013199746, 992581862, 972399545, 952642817, 933301971, 914367555, 895830370, 877681459, 859912097, 842513786, 825478247, 808797410, 792463413, 776468591, 760805470, 745466763, 730445364, 715734340, 701326928, 687216531, 673396711, 659861183, 646603816, 633618622, 620899755, 608441510, 596238312, 584284719, 572575415, 561105207, 549869021, 538861902, 528079006, 517515600, 507167059, 497028864, 487096596, 477365936, 467832661, 458492645]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1163).prefactor = (5386986442960211/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1163).cutoff/(generalMeanRows 1163).c)).2 =
    (492275344786291/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1163).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1163).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1163).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1163

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1163).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1163).criticalRate j.val*(generalMeanRows 1163).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1163).c*(generalMeanRows 1163).criticalPoint j.val)).2-
      (generalMeanRows 1163).J/2-(generalMeanRows 1163).error (generalMeanGrid j.val)+
      (generalMeanRows 1163).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1163).c)).2-
      (generalMeanRows 1163).J/2-(generalMeanRows 1163).error 4 := by
  have he : (generalMeanRows 1163).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1163) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1163)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1163

/-! Kernel-checked entropy margins for general spectral rectangle 1164. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1164
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6558209152, 6368255036, 6185854994, 6010586819, 5842059101, 5679908462, 5523797092, 5373410549, 5228455778, 5088659338, 4953765800, 4823536303, 4697747244, 4576189093, 4458665318, 4344991401, 4234993949, 4128509872, 4025385648, 3925476628, 3828646420, 3734766308, 3643714731, 3555376789, 3469643800, 3386412889, 3305586603, 3227072563, 3150783132, 3076635123, 3004549513, 2934451184, 2866268686, 2799934014, 2735382397, 2672552109, 2611384285, 2551822759, 2493813904, 2437306490, 2382251545, 2328602229, 2276313720, 2225343097, 2175649240, 2127192732, 2079935770, 2033842079, 1988876830, 1945006570, 1902199147, 1860423646, 1819650330, 1779850577, 1740996828, 1703062535, 1666022112, 1629850891, 1594525076, 1560021708, 1526318618, 1493394399, 1461228370, 1429800539, 1399091580, 1369082797, 1339756104, 1311093992, 1283079511, 1255696242, 1228928277, 1202760201, 1177177067, 1152164380, 1127708082, 1103794528, 1080410479, 1057543078, 1035179842, 1013308645, 991917706, 970995575, 950531122, 930513528, 910932270, 891777112, 873038096, 854705533, 836769993, 819222295, 802053500, 785254905, 768818033, 752734625, 736996635, 721596223, 706525748, 691777762, 677345004, 663220394, 649397030, 635868178, 622627271, 609667904, 596983826, 584568939, 572417291, 560523076, 548880623, 537484400, 526329004, 515409161, 504719720, 494255654, 484012051, 473984113, 464167156, 454556603, 445147983, 435936929, 426919171]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1164).prefactor = (706006306893153/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1164).cutoff/(generalMeanRows 1164).c)).2 =
    (60218616474913/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1164).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1164).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1164).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1164

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1164).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1164).criticalRate j.val*(generalMeanRows 1164).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1164).c*(generalMeanRows 1164).criticalPoint j.val)).2-
      (generalMeanRows 1164).J/2-(generalMeanRows 1164).error (generalMeanGrid j.val)+
      (generalMeanRows 1164).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1164).c)).2-
      (generalMeanRows 1164).J/2-(generalMeanRows 1164).error 4 := by
  have he : (generalMeanRows 1164).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1164) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1164)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1164

/-! Kernel-checked entropy margins for general spectral rectangle 1165. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1165
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6683064593, 6484636767, 6294173188, 6111229561, 5935393892, 5766283595, 5603542910, 5446840596, 5295867859, 5150336494, 5009977208, 4874538104, 4743783311, 4617491744, 4495455972, 4377481193, 4263384297, 4152993012, 4046145121, 3942687749, 3842476702, 3745375871, 3651256674, 3559997547, 3471483475, 3385605560, 3302260622, 3221350825, 3142783341, 3066470029, 2992327147, 2920275073, 2850238061, 2782143998, 2715924195, 2651513177, 2588848496, 2527870559, 2468522458, 2410749823, 2354500675, 2299725294, 2246376097, 2194407515, 2143775892, 2094439377, 2046357831, 1999492736, 1953807112, 1909265437, 1865833576, 1823478707, 1782169259, 1741874849, 1702566223, 1664215206, 1626794646, 1590278367, 1554641125, 1519858565, 1485907176, 1452764261, 1420407893, 1388816884, 1357970754, 1327849699, 1298434562, 1269706805, 1241648485, 1214242229, 1187471209, 1161319121, 1135770165, 1110809024, 1086420844, 1062591219, 1039306170, 1016552133, 994315940, 972584806, 951346314, 930588405, 910299357, 890467783, 871082613, 852133084, 833608731, 815499373, 797795109, 780486304, 763563584, 747017822, 730840135, 715021874, 699554618, 684430164, 669640523, 655177911, 641034745, 627203634, 613677377, 600448953, 587511519, 574858404, 562483103, 550379270, 538540721, 526961419, 515635480, 504557160, 493720857, 483121105, 472752569, 462610043, 452688446, 442982819, 433488322, 424200228, 415113924, 406224905, 397528773]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1165).prefactor = (5921766145440027/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1165).cutoff/(generalMeanRows 1165).c)).2 =
    (58916521367631/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1165).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1165).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1165).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1165

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1165).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1165).criticalRate j.val*(generalMeanRows 1165).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1165).c*(generalMeanRows 1165).criticalPoint j.val)).2-
      (generalMeanRows 1165).J/2-(generalMeanRows 1165).error (generalMeanGrid j.val)+
      (generalMeanRows 1165).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1165).c)).2-
      (generalMeanRows 1165).J/2-(generalMeanRows 1165).error 4 := by
  have he : (generalMeanRows 1165).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1165) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1165)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1165

/-! Kernel-checked entropy margins for general spectral rectangle 1166. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1166
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6327814261, 6150318368, 5979795886, 5815851864, 5658120727, 5506263615, 5359966002, 5218935579, 5082900337, 4951606868, 4824818812, 4702315471, 4583890551, 4469351018, 4358516065, 4251216173, 4147292251, 4046594857, 3948983482, 3854325903, 3762497580, 3673381109, 3586865725, 3502846832, 3421225587, 3341908501, 3264807083, 3189837510, 3116920312, 3045980098, 2976945285, 2909747862, 2844323162, 2780609652, 2718548745, 2658084613, 2599164028, 2541736199, 2485752637, 2431167010, 2377935028, 2326014320, 2275364328, 2225946204, 2177722717, 2130658164, 2084718287, 2039870195, 1996082293, 1953324213, 1911566752, 1870781811, 1830942340, 1792022285, 1753996540, 1716840899, 1680532014, 1645047355, 1610365168, 1576464444, 1543324879, 1510926848, 1479251369, 1448280079, 1417995204, 1388379537, 1359416407, 1331089667, 1303383661, 1276283211, 1249773597, 1223840535, 1198470163, 1173649025, 1149364052, 1125602549, 1102352182, 1079600965, 1057337242, 1035549684, 1014227267, 993359270, 972935259, 952945079, 933378845, 914226932, 895479965, 877128814, 859164583, 841578603, 824362428, 807507821, 791006755, 774851403, 759034129, 743547489, 728384220, 713537234, 698999618, 684764624, 670825665, 657176315, 643810297, 630721483, 617903892, 605351681, 593059143, 581020705, 569230924, 557684480, 546376178, 535300941, 524453807, 513829928, 503424565, 493233088, 483250969, 473473784, 463897207, 454517007, 445329051]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1166).prefactor = (671583406024829/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1166).cutoff/(generalMeanRows 1166).c)).2 =
    (262699696105663/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1166).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1166).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1166).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1166

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1166).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1166).criticalRate j.val*(generalMeanRows 1166).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1166).c*(generalMeanRows 1166).criticalPoint j.val)).2-
      (generalMeanRows 1166).J/2-(generalMeanRows 1166).error (generalMeanGrid j.val)+
      (generalMeanRows 1166).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1166).c)).2-
      (generalMeanRows 1166).J/2-(generalMeanRows 1166).error 4 := by
  have he : (generalMeanRows 1166).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1166) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1166)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1166

/-! Kernel-checked entropy margins for general spectral rectangle 1167. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1167
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6410984380, 6226538627, 6049406784, 5879175602, 5715462461, 5557912601, 5406196641, 5260008375, 5119062781, 4983094241, 4851854937, 4725113396, 4602653188, 4484271729, 4369779210, 4258997615, 4151759823, 4047908805, 3947296870, 3849784990, 3755242179, 3663544919, 3574576637, 3488227224, 3404392592, 3322974268, 3243879015, 3167018485, 3092308904, 3019670770, 2949028583, 2880310589, 2813448547, 2748377511, 2685035628, 2623363948, 2563306255, 2504808899, 2447820649, 2392292551, 2338177798, 2285431607, 2234011107, 2183875230, 2134984615, 2087301514, 2040789703, 1995414404, 1951142210, 1907941010, 1865779924, 1824629241, 1784460363, 1745245744, 1706958843, 1669574074, 1633066758, 1597413086, 1562590072, 1528575518, 1495347980, 1462886729, 1431171723, 1400183577, 1369903532, 1340313430, 1311395687, 1283133271, 1255509679, 1228508911, 1202115458, 1176314274, 1151090763, 1126430759, 1102320511, 1078746666, 1055696257, 1033156682, 1011115699, 989561407, 968482236, 947866935, 927704560, 907984466, 888696293, 869829961, 851375653, 833323817, 815665148, 798390583, 781491296, 764958688, 748784377, 732960198, 717478191, 702330595, 687509845, 673008565, 658819560, 644935812, 631350478, 618056880, 605048502, 592318989, 579862134, 567671885, 555742331, 544067702, 532642367, 521460826, 510517711, 499807778, 489325907, 479067098, 469026466, 459199240, 449580761, 440166473, 430951931, 421932787, 413104795]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1167).prefactor = (5600768411503257/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1167).cutoff/(generalMeanRows 1167).c)).2 =
    (32193126409529/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1167).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1167).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1167).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1167

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1167).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1167).criticalRate j.val*(generalMeanRows 1167).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1167).c*(generalMeanRows 1167).criticalPoint j.val)).2-
      (generalMeanRows 1167).J/2-(generalMeanRows 1167).error (generalMeanGrid j.val)+
      (generalMeanRows 1167).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1167).c)).2-
      (generalMeanRows 1167).J/2-(generalMeanRows 1167).error 4 := by
  have he : (generalMeanRows 1167).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1167) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1167)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1167

/-! Kernel-checked entropy margins for general spectral rectangle 1168. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1168
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6588737697, 6396808062, 6212525242, 6035457620, 5865205516, 5701398294, 5543691792, 5391766010, 5245323046, 5104085237, 4967793490, 4836205764, 4709095712, 4586251440, 4467474380, 4352578277, 4241388252, 4133739954, 4029478788, 3928459207, 3830544059, 3735603993, 3643516918, 3554167492, 3467446670, 3383251272, 3301483591, 3222051038, 3144865799, 3069844533, 2996908084, 2925981215, 2856992367, 2789873428, 2724559523, 2660988819, 2599102343, 2538843814, 2480159481, 2422997980, 2367310200, 2313049148, 2260169836, 2208629170, 2158385842, 2109400237, 2061634344, 2015051663, 1969617136, 1925297065, 1882059047, 1839871903, 1798705625, 1758531311, 1719321112, 1681048186, 1643686645, 1607211511, 1571598676, 1536824859, 1502867571, 1469705076, 1437316363, 1405681108, 1374779649, 1344592955, 1315102602, 1286290742, 1258140088, 1230633883, 1203755884, 1177490336, 1151821961, 1126735931, 1102217856, 1078253767, 1054830096, 1031933668, 1009551679, 987671688, 966281605, 945369670, 924924454, 904934836, 885389999, 866279418, 847592851, 829320328, 811452143, 793978845, 776891232, 760180338, 743837431, 727854003, 712221764, 696932634, 681978737, 667352397, 653046128, 639052632, 625364793, 611975669, 598878489, 586066651, 573533709, 561273378, 549279524, 537546159, 526067442, 514837669, 503851275, 493102826, 482587017, 472298668, 462232721, 452384240, 442748399, 433320491, 424095914, 415070176, 406238888]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1168).prefactor = (91227403186617/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1168).cutoff/(generalMeanRows 1168).c)).2 =
    (509974921885693/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1168).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1168).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1168).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1168

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1168).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1168).criticalRate j.val*(generalMeanRows 1168).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1168).c*(generalMeanRows 1168).criticalPoint j.val)).2-
      (generalMeanRows 1168).J/2-(generalMeanRows 1168).error (generalMeanGrid j.val)+
      (generalMeanRows 1168).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1168).c)).2-
      (generalMeanRows 1168).J/2-(generalMeanRows 1168).error 4 := by
  have he : (generalMeanRows 1168).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1168) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1168)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1168

/-! Kernel-checked entropy margins for general spectral rectangle 1169. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1169
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6771556832, 6571867903, 6380173223, 6196021976, 6018996645, 5848710003, 5684802428, 5526939498, 5374809843, 5228123203, 5086608691, 4950013214, 4818100050, 4690647565, 4567448032, 4448306574, 4333040192, 4221476880, 4113454818, 4008821636, 3907433731, 3809155652, 3713859530, 3621424554, 3531736486, 3444687224, 3360174388, 3278100947, 3198374865, 3120908784, 3045619725, 2972428809, 2901261005, 2832044891, 2764712435, 2699198789, 2635442100, 2573383334, 2512966109, 2454136546, 2396843122, 2341036538, 2286669599, 2233697090, 2182075676, 2131763795, 2082721564, 2034910694, 1988294403, 1942837339, 1898505509, 1855266210, 1813087960, 1771940446, 1731794460, 1692621851, 1654395472, 1617089131, 1580677552, 1545136328, 1510441885, 1476571443, 1443502980, 1411215200, 1379687505, 1348899957, 1318833259, 1289468723, 1260788244, 1232774282, 1205409834, 1178678416, 1152564038, 1127051190, 1102124823, 1077770327, 1053973520, 1030720627, 1007998271, 985793453, 964093543, 942886262, 922159674, 901902173, 882102471, 862749588, 843832838, 825341826, 807266434, 789596812, 772323369, 755436768, 738927915, 722787951, 707008248, 691580398, 676496208, 661747695, 647327076, 633226767, 619439372, 605957680, 592774662, 579883460, 567277387, 554949921, 542894699, 531105513, 519576307, 508301172, 497274341, 486490187, 475943216, 465628069, 455539512, 445672438, 436021859, 426582906, 417350827, 408320979, 399488829]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1169).prefactor = (6086434577714221/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1169).cutoff/(generalMeanRows 1169).c)).2 =
    (504885852378221/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1169).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1169).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1169).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1169

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1169).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1169).criticalRate j.val*(generalMeanRows 1169).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1169).c*(generalMeanRows 1169).criticalPoint j.val)).2-
      (generalMeanRows 1169).J/2-(generalMeanRows 1169).error (generalMeanGrid j.val)+
      (generalMeanRows 1169).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1169).c)).2-
      (generalMeanRows 1169).J/2-(generalMeanRows 1169).error 4 := by
  have he : (generalMeanRows 1169).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1169) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1169)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1169

/-! Kernel-checked entropy margins for general spectral rectangle 1170. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1170
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6670361706, 6464086509, 6266233957, 6076330291, 5893936519, 5718645274, 5550078030, 5387882595, 5231730871, 5081316844, 4936354760, 4796577498, 4661735077, 4531593318, 4405932624, 4284546870, 4167242392, 4053837065, 3944159463, 3838048087, 3735350658, 3635923471, 3539630803, 3446344361, 3355942783, 3268311175, 3183340680, 3100928089, 3020975471, 2943389839, 2868082840, 2794970460, 2723972762, 2655013634, 2588020560, 2522924405, 2459659213, 2398162028, 2338372712, 2280233793, 2223690307, 2168689664, 2115181514, 2063117624, 2012451766, 1963139610, 1915138622, 1868407971, 1822908442, 1778602353, 1735453478, 1693426974, 1652489314, 1612608220, 1573752607, 1535892524, 1498999099, 1463044493, 1428001849, 1393845248, 1360549668, 1328090944, 1296445729, 1265591460, 1235506325, 1206169227, 1177559760, 1149658176, 1122445359, 1095902802, 1070012578, 1044757320, 1020120200, 996084904, 972635617, 949757002, 927434181, 905652720, 884398610, 863658254, 843418454, 823666389, 804389613, 785576031, 767213893, 749291783, 731798603, 714723565, 698056182, 681786257, 665903869, 650399374, 635263387, 620486776, 606060658, 591976385, 578225543, 564799940, 551691601, 538892761, 526395859, 514193533, 502278612, 490644111, 479283225, 468189327, 457355959, 446776828, 436445801, 426356905, 416504314, 406882353, 397485489, 388308327, 379345611, 370592214, 362043137, 353693508, 345538574, 337573701, 329794370]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1170).prefactor = (6344839340826923/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1170).cutoff/(generalMeanRows 1170).c)).2 =
    (484784673057133/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1170).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1170).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1170).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1170

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1170).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1170).criticalRate j.val*(generalMeanRows 1170).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1170).c*(generalMeanRows 1170).criticalPoint j.val)).2-
      (generalMeanRows 1170).J/2-(generalMeanRows 1170).error (generalMeanGrid j.val)+
      (generalMeanRows 1170).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1170).c)).2-
      (generalMeanRows 1170).J/2-(generalMeanRows 1170).error 4 := by
  have he : (generalMeanRows 1170).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1170) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1170)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1170

/-! Kernel-checked entropy margins for general spectral rectangle 1171. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1171
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6570060319, 6384043557, 6205333436, 6033513129, 5868197282, 5709029135, 5555677942, 5407836667, 5265219927, 5127562133, 4994615830, 4866150186, 4741949636, 4621812657, 4505550646, 4392986910, 4283955748, 4178301611, 4075878335, 3976548445, 3880182517, 3786658592, 3695861642, 3607683078, 3522020299, 3438776277, 3357859178, 3279182008, 3202662289, 3128221763, 3055786114, 2985284716, 2916650392, 2849819202, 2784730239, 2721325438, 2659549410, 2599349274, 2540674513, 2483476828, 2427710017, 2373329850, 2320293955, 2268561720, 2218094190, 2168853978, 2120805181, 2073913300, 2028145168, 1983468876, 1939853714, 1897270106, 1855689557, 1815084594, 1775428723, 1736696376, 1698862872, 1661904372, 1625797839, 1590521008, 1556052342, 1522371008, 1489456841, 1457290317, 1425852525, 1395125144, 1365090413, 1335731113, 1307030543, 1278972499, 1251541257, 1224721549, 1198498553, 1172857869, 1147785508, 1123267875, 1099291753, 1075844293, 1052913000, 1030485716, 1008550617, 987096191, 966111237, 945584850, 925506410, 905865577, 886652275, 867856693, 849469269, 831480684, 813881856, 796663933, 779818282, 763336488, 747210343, 731431843, 715993179, 700886735, 686105078, 671640958, 657487297, 643637189, 630083893, 616820830, 603841575, 591139856, 578709550, 566544677, 554639398, 542988010, 531584943, 520424756, 509502135, 498811886, 488348940, 478108338, 468085240, 458274914, 448672736, 439274189, 430074855]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1171).prefactor = (5757373448701411/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1171).cutoff/(generalMeanRows 1171).c)).2 =
    (34653680926807/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1171).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1171).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1171).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1171

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1171).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1171).criticalRate j.val*(generalMeanRows 1171).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1171).c*(generalMeanRows 1171).criticalPoint j.val)).2-
      (generalMeanRows 1171).J/2-(generalMeanRows 1171).error (generalMeanGrid j.val)+
      (generalMeanRows 1171).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1171).c)).2-
      (generalMeanRows 1171).J/2-(generalMeanRows 1171).error 4 := by
  have he : (generalMeanRows 1171).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1171) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1171)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1171

/-! Kernel-checked entropy margins for general spectral rectangle 1172. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1172
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7115743568, 6921855428, 6735475703, 6556174323, 6383553877, 6217246611, 6056911750, 5902233104, 5752916922, 5608689965, 5469297779, 5334503123, 5204084562, 5077835190, 4955561468, 4837082175, 4722227450, 4610837921, 4502763912, 4397864716, 4296007934, 4197068868, 4100929965, 4007480307, 3916615145, 3828235466, 3742247601, 3658562856, 3577097182, 3497770863, 3420508230, 3345237397, 3271890019, 3200401066, 3130708612, 3062753643, 2996479878, 2931833605, 2868763519, 2807220588, 2747157912, 2688530602, 2631295667, 2575411902, 2520839790, 2467541409, 2415480343, 2364621603, 2314931550, 2266377821, 2218929269, 2172555895, 2127228792, 2082920090, 2039602906, 1997251294, 1955840201, 1915345425, 1875743576, 1837012035, 1799128924, 1762073068, 1725823968, 1690361768, 1655667229, 1621721703, 1588507108, 1556005903, 1524201070, 1493076088, 1462614917, 1432801977, 1403622131, 1375060671, 1347103294, 1319736098, 1292945556, 1266718511, 1241042160, 1215904039, 1191292016, 1167194275, 1143599309, 1120495907, 1097873146, 1075720380, 1054027232, 1032783587, 1011979579, 991605590, 971652236, 952110363, 932971039, 914225551, 895865391, 877882257, 860268045, 843014840, 826114918, 809560730, 793344909, 777460256, 761899737, 746656484, 731723784, 717095078, 702763955, 688724151, 674969543, 661494146, 648292108, 635357710, 622685359, 610269586, 598105045, 586186507, 574508857, 563067094, 551856326, 540871769, 530108742]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1172).prefactor = (2987404514141331/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1172).cutoff/(generalMeanRows 1172).c)).2 =
    (569687615530739/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1172).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1172).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1172).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1172

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1172).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1172).criticalRate j.val*(generalMeanRows 1172).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1172).c*(generalMeanRows 1172).criticalPoint j.val)).2-
      (generalMeanRows 1172).J/2-(generalMeanRows 1172).error (generalMeanGrid j.val)+
      (generalMeanRows 1172).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1172).c)).2-
      (generalMeanRows 1172).J/2-(generalMeanRows 1172).error 4 := by
  have he : (generalMeanRows 1172).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1172) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1172)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1172

/-! Kernel-checked entropy margins for general spectral rectangle 1173. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1173
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7594489479, 7395655209, 7204417882, 7020340136, 6843018012, 6672077875, 6507173670, 6347984466, 6194212263, 6045580014, 5901829850, 5762721481, 5628030745, 5497548303, 5371078449, 5248438037, 5129455497, 5013969945, 4901830371, 4792894896, 4687030094, 4584110369, 4484017391, 4386639569, 4291871579, 4199613919, 4109772506, 4022258306, 3936986988, 3853878612, 3772857333, 3693851135, 3616791578, 3541613574, 3468255169, 3396657348, 3326763850, 3258521002, 3191877560, 3126784559, 3063195186, 3001064645, 2940350044, 2881010287, 2823005969, 2766299282, 2710853928, 2656635035, 2603609081, 2551743820, 2501008217, 2451372386, 2402807527, 2355285873, 2308780642, 2263265981, 2218716926, 2175109360, 2132419969, 2090626207, 2049706259, 2009639011, 1970404014, 1931981458, 1894352144, 1857497455, 1821399335, 1786040261, 1751403226, 1717471716, 1684229688, 1651661555, 1619752165, 1588486788, 1557851097, 1527831152, 1498413391, 1469584610, 1441331954, 1413642904, 1386505265, 1359907153, 1333836988, 1308283483, 1283235629, 1258682695, 1234614211, 1211019964, 1187889989, 1165214560, 1142984185, 1121189597, 1099821747, 1078871799, 1058331123, 1038191289, 1018444062, 999081394, 980095422, 961478460, 943222997, 925321689, 907767357, 890552982, 873671699, 857116794, 840881704, 824960004, 809345414, 794031786, 779013108, 764283496, 749837191, 735668559, 721772086, 708142374, 694774140, 681662212, 668801527, 656187128, 643814163]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1173).prefactor = (6109192435440917/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1173).cutoff/(generalMeanRows 1173).c)).2 =
    (585151841228321/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1173).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1173).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1173).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1173

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1173).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1173).criticalRate j.val*(generalMeanRows 1173).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1173).c*(generalMeanRows 1173).criticalPoint j.val)).2-
      (generalMeanRows 1173).J/2-(generalMeanRows 1173).error (generalMeanGrid j.val)+
      (generalMeanRows 1173).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1173).c)).2-
      (generalMeanRows 1173).J/2-(generalMeanRows 1173).error 4 := by
  have he : (generalMeanRows 1173).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1173) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1173)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1173

/-! Kernel-checked entropy margins for general spectral rectangle 1174. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1174
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5973710831, 5779228162, 5592870359, 5414176817, 5242721003, 5078107368, 4919968588, 4767963094, 4621772867, 4481101445, 4345672135, 4215226400, 4089522400, 3968333667, 3851447907, 3738665912, 3629800566, 3524675942, 3423126474, 3324996210, 3230138115, 3138413439, 3049691144, 2963847363, 2880764916, 2800332858, 2722446063, 2647004843, 2573914593, 2503085467, 2434432074, 2367873203, 2303331559, 2240733527, 2180008950, 2121090921, 2063915592, 2008421998, 1954551887, 1902249567, 1851461767, 1802137494, 1754227916, 1707686242, 1662467610, 1618528990, 1575829086, 1534328245, 1493988377, 1454772873, 1416646532, 1379575495, 1343527175, 1308470199, 1274374351, 1241210515, 1208950628, 1177567629, 1147035414, 1117328795, 1088423460, 1060295930, 1032923529, 1006284349, 980357214, 955121653, 930557868, 906646711, 883369655, 860708769, 838646696, 817166628, 796252290, 775887915, 756058226, 736748418, 717944143, 699631487, 681796963, 664427486, 647510368, 631033297, 614984327, 599351866, 584124661, 569291788, 554842644, 540766930, 527054645, 513696078, 500681791, 488002620, 475649659, 463614252, 451887991, 440462700, 429330436, 418483475, 407914309, 397615636, 387580358, 377801573, 368272568, 358986813, 349937957, 341119824, 332526404, 324151851, 315990477, 308036747, 300285277, 292730827, 285368297, 278192724, 271199278, 264383258, 257740088, 251265315, 244954601, 238803727, 232808582]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1174).prefactor = (6200456378680767/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1174).cutoff/(generalMeanRows 1174).c)).2 =
    (247881170916861/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1174).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1174).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1174).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1174

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1174).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1174).criticalRate j.val*(generalMeanRows 1174).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1174).c*(generalMeanRows 1174).criticalPoint j.val)).2-
      (generalMeanRows 1174).J/2-(generalMeanRows 1174).error (generalMeanGrid j.val)+
      (generalMeanRows 1174).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1174).c)).2-
      (generalMeanRows 1174).J/2-(generalMeanRows 1174).error 4 := by
  have he : (generalMeanRows 1174).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1174) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1174)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1174

/-! Kernel-checked entropy margins for general spectral rectangle 1175. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1175
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6034909529, 5856711771, 5685593754, 5521150780, 5363009027, 5210822690, 5064271418, 4923058034, 4786906495, 4655560051, 4528779602, 4406342212, 4288039764, 4173677755, 4063074193, 3956058605, 3852471135, 3752161719, 3654989339, 3560821338, 3469532805, 3381005996, 3295129821, 3211799365, 3130915449, 3052384234, 2976116845, 2902029043, 2830040902, 2760076530, 2692063802, 2625934115, 2561622164, 2499065733, 2438205503, 2378984871, 2321349792, 2265248617, 2210631957, 2157452550, 2105665136, 2055226348, 2006094601, 1958229997, 1911594231, 1866150507, 1821863455, 1778699062, 1736624595, 1695608543, 1655620551, 1616631363, 1578612771, 1541537564, 1505379481, 1470113163, 1435714117, 1402158674, 1369423953, 1337487823, 1306328877, 1275926394, 1246260316, 1217311214, 1189060269, 1161489242, 1134580454, 1108316762, 1082681538, 1057658652, 1033232449, 1009387735, 986109757, 963384189, 941197114, 919535014, 898384751, 877733556, 857569016, 837879063, 818651961, 799876294, 781540958, 763635150, 746148356, 729070344, 712391157, 696101099, 680190730, 664650861, 649472540, 634647049, 620165896, 606020809, 592203729, 578706802, 565522376, 552642993, 540061383, 527770463, 515763325, 504033236, 492573632, 481378113, 470440436, 459754517, 449314419, 439114354, 429148676, 419411877, 409898585, 400603559, 391521688, 382647982, 373977575, 365505718, 357227778, 349139233, 341235672, 333512787, 325966377]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1175).prefactor = (5668193738342571/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1175).cutoff/(generalMeanRows 1175).c)).2 =
    (286576911753613/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1175).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1175).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1175).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1175

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1175).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1175).criticalRate j.val*(generalMeanRows 1175).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1175).c*(generalMeanRows 1175).criticalPoint j.val)).2-
      (generalMeanRows 1175).J/2-(generalMeanRows 1175).error (generalMeanGrid j.val)+
      (generalMeanRows 1175).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1175).c)).2-
      (generalMeanRows 1175).J/2-(generalMeanRows 1175).error 4 := by
  have he : (generalMeanRows 1175).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1175) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1175)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1175

/-! Kernel-checked entropy margins for general spectral rectangle 1176. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1176
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6418234156, 6233186579, 6055414661, 5884501826, 5720063404, 5561743662, 5409213164, 5262166400, 5120319680, 4983409229, 4851189485, 4723431558, 4599921850, 4480460794, 4364861723, 4252949842, 4144561292, 4039542298, 3937748401, 3839043750, 3743300458, 3650398015, 3560222750, 3472667340, 3387630356, 3305015850, 3224732979, 3146695647, 3070822190, 2997035080, 2925260647, 2855428833, 2787472956, 2721329497, 2656937903, 2594240399, 2533181822, 2473709463, 2415772919, 2359323959, 2304316398, 2250705980, 2198450267, 2147508541, 2097841710, 2049412215, 2002183954, 1956122202, 1911193541, 1867365790, 1824607949, 1782890133, 1742183523, 1702460312, 1663693657, 1625857633, 1588927194, 1552878128, 1517687023, 1483331230, 1449788833, 1417038611, 1385060014, 1353833135, 1323338678, 1293557941, 1264472784, 1236065615, 1208319362, 1181217456, 1154743811, 1128882807, 1103619271, 1078938464, 1054826062, 1031268140, 1008251163, 985761970, 963787759, 942316077, 921334809, 900832166, 880796672, 861217158, 842082749, 823382856, 805107166, 787245636, 769788480, 752726165, 736049404, 719749143, 703816562, 688243062, 673020259, 658139982, 643594262, 629375329, 615475607, 601887705, 588604416, 575618708, 562923722, 550512766, 538379312, 526516989, 514919580, 503581019, 492495384, 481656898, 471059920, 460698945, 450568598, 440663632, 430978925, 421509477, 412250405, 403196940, 394344428, 385688323, 377224184]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1176).prefactor = (1172121681201799/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1176).cutoff/(generalMeanRows 1176).c)).2 =
    (116572527526837/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1176).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1176).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1176).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1176

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1176).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1176).criticalRate j.val*(generalMeanRows 1176).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1176).c*(generalMeanRows 1176).criticalPoint j.val)).2-
      (generalMeanRows 1176).J/2-(generalMeanRows 1176).error (generalMeanGrid j.val)+
      (generalMeanRows 1176).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1176).c)).2-
      (generalMeanRows 1176).J/2-(generalMeanRows 1176).error 4 := by
  have he : (generalMeanRows 1176).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1176) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1176)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1176

/-! Kernel-checked entropy margins for general spectral rectangle 1177. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1177
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6139878533, 5971899352, 5810426997, 5655091247, 5505549758, 5361485511, 5222604543, 5088633909, 4959319862, 4834426215, 4713732871, 4597034489, 4484139290, 4374867961, 4269052676, 4166536200, 4067171068, 3970818849, 3877349466, 3786640576, 3698577007, 3613050236, 3529957917, 3449203444, 3370695548, 3294347934, 3220078933, 3147811200, 3077471417, 3008990032, 2942301012, 2877341614, 2814052179, 2752375932, 2692258808, 2633649279, 2576498202, 2520758676, 2466385904, 2413337075, 2361571241, 2311049214, 2261733467, 2213588034, 2166578431, 2120671568, 2075835676, 2032040236, 1989255911, 1947454487, 1906608813, 1866692744, 1827681094, 1789549590, 1752274818, 1715834193, 1680205909, 1645368908, 1611302844, 1577988048, 1545405499, 1513536796, 1482364127, 1451870245, 1422038445, 1392852539, 1364296835, 1336356115, 1309015618, 1282261021, 1256078418, 1230454309, 1205375581, 1180829492, 1156803661, 1133286050, 1110264956, 1087728993, 1065667088, 1044068462, 1022922626, 1002219366, 981948739, 962101059, 942666889, 923637037, 905002543, 886754675, 868884918, 851384972, 834246740, 817462327, 801024031, 784924335, 769155907, 753711589, 738584397, 723767510, 709254271, 695038179, 681112887, 667472193, 654110043, 641020520, 628197846, 615636373, 603330585, 591275088, 579464615, 567894014, 556558250, 545452404, 534571663, 523911325, 513466788, 503233557, 493207233, 483383516, 473758199, 464327168, 455086399]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1177).prefactor = (4007043095747/781250000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1177).cutoff/(generalMeanRows 1177).c)).2 =
    (138545857248693/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1177).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1177).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1177).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1177

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1177).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1177).criticalRate j.val*(generalMeanRows 1177).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1177).c*(generalMeanRows 1177).criticalPoint j.val)).2-
      (generalMeanRows 1177).J/2-(generalMeanRows 1177).error (generalMeanGrid j.val)+
      (generalMeanRows 1177).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1177).c)).2-
      (generalMeanRows 1177).J/2-(generalMeanRows 1177).error 4 := by
  have he : (generalMeanRows 1177).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1177) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1177)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1177

/-! Kernel-checked entropy margins for general spectral rectangle 1178. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1178
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6236087787, 6061054566, 5892864867, 5731130362, 5575491860, 5425616639, 5281196079, 5141943534, 5007592436, 4877894585, 4752618609, 4631548583, 4514482766, 4401232477, 4291621057, 4185482938, 4082662790, 3983014747, 3886401699, 3792694648, 3701772110, 3613519582, 3527829040, 3444598484, 3363731522, 3285136981, 3208728555, 3134424476, 3062147217, 2991823207, 2923382581, 2856758936, 2791889118, 2728713010, 2667173350, 2607215554, 2548787552, 2491839639, 2436324332, 2382196245, 2329411962, 2277929926, 2227710335, 2178715044, 2130907468, 2084252507, 2038716454, 1994266929, 1950872808, 1908504154, 1867132159, 1826729084, 1787268211, 1748723785, 1711070973, 1674285815, 1638345187, 1603226756, 1568908949, 1535370915, 1502592491, 1470554177, 1439237098, 1408622987, 1378694149, 1349433444, 1320824261, 1292850496, 1265496531, 1238747215, 1212587848, 1187004157, 1161982288, 1137508780, 1113570561, 1090154924, 1067249519, 1044842339, 1022921707, 1001476265, 980494962, 959967043, 939882041, 920229767, 901000296, 882183966, 863771362, 845753315, 828120887, 810865369, 793978272, 777451320, 761276443, 745445772, 729951633, 714786540, 699943191, 685414459, 671193392, 657273205, 643647275, 630309139, 617252487, 604471156, 591959133, 579710543, 567719650, 555980851, 544488674, 533237773, 522222927, 511439034, 500881109, 490544282, 480423794, 470514993, 460813335, 451314376, 442013774, 432907285, 423990759]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1178).prefactor = (2679662742636501/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1178).cutoff/(generalMeanRows 1178).c)).2 =
    (544005224079017/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1178).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1178).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1178).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1178

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1178).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1178).criticalRate j.val*(generalMeanRows 1178).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1178).c*(generalMeanRows 1178).criticalPoint j.val)).2-
      (generalMeanRows 1178).J/2-(generalMeanRows 1178).error (generalMeanGrid j.val)+
      (generalMeanRows 1178).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1178).c)).2-
      (generalMeanRows 1178).J/2-(generalMeanRows 1178).error 4 := by
  have he : (generalMeanRows 1178).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1178) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1178)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1178

/-! Kernel-checked entropy margins for general spectral rectangle 1179. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1179
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6424482536, 6241885559, 6066461937, 5897805110, 5735538963, 5579315046, 5428810101, 5283723841, 5143776968, 5008709385, 4878278597, 4752258255, 4630436851, 4512616533, 4398612026, 4288249660, 4181366476, 4077809419, 3977434599, 3880106616, 3785697939, 3694088345, 3605164395, 3518818964, 3434950795, 3353464105, 3274268210, 3197277181, 3122409535, 3049587939, 2978738943, 2909792732, 2842682895, 2777346213, 2713722460, 2651754221, 2591386722, 2532567671, 2475247113, 2419377292, 2364912524, 2311809080, 2260025075, 2209520363, 2160256445, 2112196378, 2065304690, 2019547303, 1974891457, 1931305649, 1888759559, 1847223998, 1806670846, 1767073004, 1728404340, 1690639646, 1653754591, 1617725682, 1582530225, 1548146289, 1514552668, 1481728853, 1449655002, 1418311904, 1387680962, 1357744158, 1328484036, 1299883672, 1271926659, 1244597083, 1217879501, 1191758929, 1166220817, 1141251039, 1116835873, 1092961986, 1069616422, 1046786586, 1024460232, 1002625453, 981270663, 960384593, 939956276, 919975036, 900430482, 881312495, 862611222, 844317065, 826420674, 808912939, 791784982, 775028151, 758634012, 742594342, 726901125, 711546542, 696522968, 681822965, 667439280, 653364832, 639592716, 626116191, 612928681, 600023765, 587395177, 575036800, 562942660, 551106927, 539523906, 528188038, 517093891, 506236162, 495609670, 485209355, 475030275, 465067598, 455316607, 445772693, 436431349, 427288174, 418338866]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1179).prefactor = (1119995505834387/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1179).cutoff/(generalMeanRows 1179).c)).2 =
    (538954708292947/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1179).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1179).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1179).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1179

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1179).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1179).criticalRate j.val*(generalMeanRows 1179).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1179).c*(generalMeanRows 1179).criticalPoint j.val)).2-
      (generalMeanRows 1179).J/2-(generalMeanRows 1179).error (generalMeanGrid j.val)+
      (generalMeanRows 1179).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1179).c)).2-
      (generalMeanRows 1179).J/2-(generalMeanRows 1179).error 4 := by
  have he : (generalMeanRows 1179).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1179) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1179)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1179

/-! Kernel-checked entropy margins for general spectral rectangle 1180. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1180
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6525852100, 6335754148, 6153197196, 5977754712, 5809031990, 5646663249, 5490309051, 5339653984, 5194404591, 5054287510, 4919047793, 4788447398, 4662263819, 4540288851, 4422327465, 4308196786, 4197725171, 4090751355, 3987123684, 3886699408, 3789344035, 3694930741, 3603339826, 3514458217, 3428179010, 3344401050, 3263028542, 3183970693, 3107141387, 3032458872, 2959845488, 2889227400, 2820534360, 2753699483, 2688659042, 2625352274, 2563721199, 2503710463, 2445267175, 2388340769, 2332882868, 2278847164, 2226189295, 2174866745, 2124838736, 2076066141, 2028511389, 1982138388, 1936912444, 1892800193, 1849769531, 1807789548, 1766830477, 1726863627, 1687861341, 1649796941, 1612644681, 1576379710, 1540978023, 1506416426, 1472672503, 1439724574, 1407551672, 1376133503, 1345450423, 1315483412, 1286214042, 1257624457, 1229697351, 1202415943, 1175763955, 1149725598, 1124285548, 1099428931, 1075141305, 1051408644, 1028217322, 1005554102, 983406116, 961760858, 940606168, 919930220, 899721512, 879968854, 860661358, 841788426, 823339745, 805305274, 787675235, 770440108, 753590618, 737117732, 721012649, 705266795, 689871812, 674819554, 660102084, 645711662, 631640741, 617881963, 604428155, 591272317, 578407625, 565827421, 553525209, 541494653, 529729570, 518223926, 506971834, 495967548, 485205459, 474680092, 464386105, 454318280, 444471525, 434840866, 425421449, 416208533, 407197488, 398383794, 389763034]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1180).prefactor = (1462858918226029/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1180).cutoff/(generalMeanRows 1180).c)).2 =
    (52892956167357/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1180).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1180).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1180).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1180

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1180).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1180).criticalRate j.val*(generalMeanRows 1180).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1180).c*(generalMeanRows 1180).criticalPoint j.val)).2-
      (generalMeanRows 1180).J/2-(generalMeanRows 1180).error (generalMeanGrid j.val)+
      (generalMeanRows 1180).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1180).c)).2-
      (generalMeanRows 1180).J/2-(generalMeanRows 1180).error 4 := by
  have he : (generalMeanRows 1180).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1180) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1180)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1180

/-! Kernel-checked entropy margins for general spectral rectangle 1181. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1181
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6723362940, 6525133725, 6334807080, 6151936398, 5976108340, 5806939802, 5644075219, 5487184143, 5335959083, 5190113560, 5049380356, 4913509931, 4782269000, 4655439235, 4532816098, 4414207768, 4299434176, 4188326120, 4080724456, 3976479365, 3875449674, 3777502239, 3682511382, 3590358365, 3500930913, 3414122779, 3329833332, 3247967186, 3168433855, 3091147436, 3016026313, 2942992884, 2871973313, 2802897290, 2735697822, 2670311026, 2606675944, 2544734374, 2484430702, 2425711756, 2368526667, 2312826737, 2258565316, 2205697695, 2154180993, 2103974063, 2055037400, 2007333050, 1960824535, 1915476773, 1871256011, 1828129754, 1786066707, 1745036713, 1705010702, 1665960634, 1627859456, 1590681052, 1554400202, 1518992542, 1484434524, 1450703381, 1417777092, 1385634352, 1354254538, 1323617686, 1293704458, 1264496117, 1235974508, 1208122028, 1180921609, 1154356695, 1128411223, 1103069603, 1078316702, 1054137827, 1030518705, 1007445475, 984904666, 962883188, 941368315, 920347676, 899809240, 879741306, 860132491, 840971720, 822248216, 803951489, 786071329, 768597795, 751521208, 734832141, 718521412, 702580078, 686999426, 671770966, 656886424, 642337739, 628117050, 614216698, 600629214, 587347317, 574363905, 561672057, 549265018, 537136203, 525279187, 513687704, 502355640, 491277029, 480446052, 469857030, 459504419, 449382812, 439486930, 429811620, 420351854, 411102721, 402059430, 393217301, 384571767]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1181).prefactor = (6114185147310377/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1181).cutoff/(generalMeanRows 1181).c)).2 =
    (104790885406691/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1181).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1181).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1181).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1181

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1181).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1181).criticalRate j.val*(generalMeanRows 1181).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1181).c*(generalMeanRows 1181).criticalPoint j.val)).2-
      (generalMeanRows 1181).J/2-(generalMeanRows 1181).error (generalMeanGrid j.val)+
      (generalMeanRows 1181).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1181).c)).2-
      (generalMeanRows 1181).J/2-(generalMeanRows 1181).error 4 := by
  have he : (generalMeanRows 1181).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1181) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1181)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1181

/-! Kernel-checked entropy margins for general spectral rectangle 1182. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1182
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6391587949, 6215490832, 6046189487, 5883295100, 5726448619, 5575317995, 5429595715, 5288996610, 5153255881, 5022127334, 4895381791, 4772805658, 4654199634, 4539377540, 4428165263, 4320399795, 4215928361, 4114607627, 4016302975, 3920887847, 3828243141, 3738256664, 3650822625, 3565841177, 3483217992, 3402863877, 3324694412, 3248629626, 3174593695, 3102514662, 3032324183, 2963957291, 2897352173, 2832449977, 2769194615, 2707532599, 2647412876, 2588786685, 2531607411, 2475830466, 2421413167, 2368314625, 2316495645, 2265918627, 2216547483, 2168347547, 2121285505, 2075329318, 2030448157, 1986612342, 1943793276, 1901963401, 1861096138, 1821165839, 1782147750, 1744017959, 1706753360, 1670331619, 1634731134, 1599931001, 1565910991, 1532651511, 1500133581, 1468338811, 1437249369, 1406847964, 1377117820, 1348042661, 1319606682, 1291794540, 1264591331, 1237982573, 1211954195, 1186492515, 1161584230, 1137216404, 1113376450, 1090052121, 1067231499, 1044902980, 1023055267, 1001677358, 980758538, 960288367, 940256673, 920653543, 901469315, 882694570, 864320124, 846337022, 828736530, 811510129, 794649509, 778146561, 761993374, 746182228, 730705586, 715556093, 700726571, 686210007, 671999559, 658088542, 644470431, 631138850, 618087574, 605310522, 592801751, 580555459, 568565974, 556827756, 545335390, 534083586, 523067171, 512281094, 501720413, 491380302, 481256040, 471343014, 461636713, 452132728, 442826746]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1182).prefactor = (219661513722051/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1182).cutoff/(generalMeanRows 1182).c)).2 =
    (11741270443551/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1182).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1182).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1182).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1182

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1182).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1182).criticalRate j.val*(generalMeanRows 1182).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1182).c*(generalMeanRows 1182).criticalPoint j.val)).2-
      (generalMeanRows 1182).J/2-(generalMeanRows 1182).error (generalMeanGrid j.val)+
      (generalMeanRows 1182).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1182).c)).2-
      (generalMeanRows 1182).J/2-(generalMeanRows 1182).error 4 := by
  have he : (generalMeanRows 1182).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1182) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1182)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1182

/-! Kernel-checked entropy margins for general spectral rectangle 1183. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1183
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6549911078, 6367169963, 6191515749, 6022543485, 5859879160, 5703176830, 5552116066, 5406399667, 5265751614, 5129915239, 4998651572, 4871737853, 4748966190, 4630142347, 4515084642, 4403622950, 4295597798, 4190859542, 4089267612, 3990689830, 3895001788, 3802086270, 3711832732, 3624136825, 3538899951, 3456028864, 3375435297, 3297035620, 3220750529, 3146504755, 3074226800, 3003848687, 2935305735, 2868536352, 2803481835, 2740086196, 2678295990, 2618060168, 2559329925, 2502058575, 2446201422, 2391715650, 2338560213, 2286695735, 2236084421, 2186689968, 2138477487, 2091413424, 2045465493, 2000602611, 1956794834, 1914013301, 1872230183, 1831418626, 1791552711, 1752607405, 1714558522, 1677382682, 1641057277, 1605560431, 1570870976, 1536968411, 1503832884, 1471445154, 1439786575, 1408839064, 1378585082, 1349007612, 1320090138, 1291816623, 1264171496, 1237139628, 1210706322, 1184857290, 1159578644, 1134856879, 1110678860, 1087031808, 1063903289, 1041281202, 1019153767, 997509514, 976337274, 955626169, 935365603, 915545251, 896155051, 877185198, 858626134, 840468542, 822703335, 805321656, 788314863, 771674528, 755392430, 739460549, 723871058, 708616320, 693688882, 679081469, 664786981, 650798487, 637109217, 623712567, 610602082, 597771463, 585214558, 572925355, 560897987, 549126718, 537605948, 526330206, 515294145, 504492541, 493920292, 483572409, 473444019, 463530359, 453826775, 444328717, 435031737]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1183).prefactor = (114151389203289/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1183).cutoff/(generalMeanRows 1183).c)).2 =
    (291050366417711/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1183).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1183).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1183).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1183

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1183).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1183).criticalRate j.val*(generalMeanRows 1183).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1183).c*(generalMeanRows 1183).criticalPoint j.val)).2-
      (generalMeanRows 1183).J/2-(generalMeanRows 1183).error (generalMeanGrid j.val)+
      (generalMeanRows 1183).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1183).c)).2-
      (generalMeanRows 1183).J/2-(generalMeanRows 1183).error 4 := by
  have he : (generalMeanRows 1183).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1183) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1183)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1183

/-! Kernel-checked entropy margins for general spectral rectangle 1184. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1184
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6525900184, 6337012606, 6155561743, 5981124000, 5813307961, 5651751412, 5496118687, 5346098300, 5201400825, 5061756990, 4926915962, 4796643806, 4670722090, 4548946626, 4431126326, 4317082169, 4206646257, 4099660961, 3995978141, 3895458430, 3797970592, 3703390921, 3611602698, 3522495695, 3435965718, 3351914183, 3270247733, 3190877884, 3113720696, 3038696473, 2965729484, 2894747707, 2825682594, 2758468850, 2693044228, 2629349347, 2567327513, 2506924561, 2448088702, 2390770389, 2334922180, 2280498628, 2227456159, 2175752975, 2125348954, 2076205560, 2028285756, 1981553931, 1935975821, 1891518441, 1848150022, 1805839949, 1764558706, 1724277822, 1684969820, 1646608172, 1609167253, 1572622302, 1536949383, 1502125344, 1468127790, 1434935043, 1402526115, 1370880680, 1339979043, 1309802118, 1280331400, 1251548944, 1223437342, 1195979705, 1169159637, 1142961222, 1117369004, 1092367970, 1067943534, 1044081521, 1020768155, 997990042, 975734157, 953987833, 932738748, 911974914, 891684665, 871856645, 852479803, 833543379, 815036894, 796950145, 779273193, 761996357, 745110205, 728605546, 712473424, 696705111, 681292099, 666226095, 651499012, 637102967, 623030273, 609273434, 595825138, 582678254, 569825826, 557261068, 544977360, 532968241, 521227411, 509748718, 498526161, 487553882, 476826165, 466337429, 456082228, 446055245, 436251289, 426665294, 417292310, 408127509, 399166173, 390403696, 381835582]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1184).prefactor = (5932099545452911/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1184).cutoff/(generalMeanRows 1184).c)).2 =
    (567358451098217/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1184).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1184).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1184).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1184

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1184).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1184).criticalRate j.val*(generalMeanRows 1184).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1184).c*(generalMeanRows 1184).criticalPoint j.val)).2-
      (generalMeanRows 1184).J/2-(generalMeanRows 1184).error (generalMeanGrid j.val)+
      (generalMeanRows 1184).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1184).c)).2-
      (generalMeanRows 1184).J/2-(generalMeanRows 1184).error 4 := by
  have he : (generalMeanRows 1184).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1184) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1184)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1184

/-! Kernel-checked entropy margins for general spectral rectangle 1185. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1185
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7075381367, 6877979744, 6688233571, 6505705413, 6329991251, 6160717389, 5997537691, 5840131111, 5688199489, 5541465565, 5399671197, 5262575753, 5129954665, 5001598113, 4877309839, 4756906070, 4640214540, 4527073598, 4417331398, 4310845159, 4207480490, 4107110772, 4009616594, 3914885233, 3822810184, 3733290718, 3646231486, 3561542151, 3479137046, 3398934863, 3320858369, 3244834132, 3170792283, 3098666289, 3028392737, 2959911147, 2893163788, 2828095513, 2764653603, 2702787627, 2642449303, 2583592379, 2526172517, 2470147182, 2415475547, 2362118397, 2310038042, 2259198238, 2209564109, 2161102077, 2113779796, 2067566091, 2022430899, 1978345212, 1935281031, 1893211316, 1852109941, 1811951648, 1772712017, 1734367417, 1696894980, 1660272564, 1624478720, 1589492667, 1555294260, 1521863968, 1489182843, 1457232504, 1425995109, 1395453336, 1365590363, 1336389849, 1307835915, 1279913130, 1252606491, 1225901408, 1199783694, 1174239544, 1149255527, 1124818570, 1100915949, 1077535274, 1054664479, 1032291815, 1010405833, 988995382, 968049592, 947557872, 927509897, 907895602, 888705172, 869929037, 851557864, 833582549, 815994211, 798784186, 781944019, 765465461, 749340461, 733561161, 718119890, 703009160, 688221662, 673750257, 659587976, 645728014, 632163724, 618888613, 605896342, 593180717, 580735687, 568555342, 556633906, 544965738, 533545324, 522367276, 511426331, 500717342, 490235283, 479975237, 469932402]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1185).prefactor = (6165462420171529/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1185).cutoff/(generalMeanRows 1185).c)).2 =
    (291050366417711/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1185).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1185).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1185).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1185

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1185).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1185).criticalRate j.val*(generalMeanRows 1185).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1185).c*(generalMeanRows 1185).criticalPoint j.val)).2-
      (generalMeanRows 1185).J/2-(generalMeanRows 1185).error (generalMeanGrid j.val)+
      (generalMeanRows 1185).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1185).c)).2-
      (generalMeanRows 1185).J/2-(generalMeanRows 1185).error 4 := by
  have he : (generalMeanRows 1185).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1185) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1185)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1185

/-! Kernel-checked entropy margins for general spectral rectangle 1186. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1186
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7662420827, 7459324043, 7263953622, 7075865488, 6894649757, 6719927558, 6551348201, 6388586638, 6231341206, 6079331583, 5932296966, 5789994419, 5652197389, 5518694356, 5389287621, 5263792199, 5142034815, 5023852993, 4909094224, 4797615210, 4689281173, 4583965219, 4481547764, 4381916002, 4284963420, 4190589353, 4098698575, 4009200921, 3922010941, 3837047585, 3754233904, 3673496782, 3594766687, 3517977434, 3443065981, 3369972222, 3298638810, 3229010986, 3161036419, 3094665065, 3029849029, 2966542441, 2904701336, 2844283547, 2785248608, 2727557651, 2671173327, 2616059718, 2562182265, 2509507692, 2458003945, 2407640124, 2358386428, 2310214101, 2263095378, 2217003439, 2171912363, 2127797089, 2084633371, 2042397743, 2001067487, 1960620597, 1921035745, 1882292260, 1844370091, 1807249789, 1770912475, 1735339825, 1700514039, 1666417828, 1633034389, 1600347389, 1568340947, 1536999616, 1506308370, 1476252582, 1446818020, 1417990824, 1389757498, 1362104894, 1335020206, 1308490952, 1282504967, 1257050392, 1232115665, 1207689509, 1183760925, 1160319185, 1137353820, 1114854613, 1092811596, 1071215034, 1050055427, 1029323497, 1009010186, 989106645, 969604234, 950494510, 931769225, 913420322, 895439925, 877820339, 860554043, 843633685, 827052079, 810802197, 794877173, 779270287, 763974974, 748984809, 734293511, 719894936, 705783074, 691952047, 678396103, 665109617, 652087085, 639323119, 626812450, 614549922, 602530487]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1186).prefactor = (3154931935136507/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1186).cutoff/(generalMeanRows 1186).c)).2 =
    (60210139954209/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1186).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1186).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1186).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1186

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1186).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1186).criticalRate j.val*(generalMeanRows 1186).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1186).c*(generalMeanRows 1186).criticalPoint j.val)).2-
      (generalMeanRows 1186).J/2-(generalMeanRows 1186).error (generalMeanGrid j.val)+
      (generalMeanRows 1186).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1186).c)).2-
      (generalMeanRows 1186).J/2-(generalMeanRows 1186).error 4 := by
  have he : (generalMeanRows 1186).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1186) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1186)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1186

/-! Kernel-checked entropy margins for general spectral rectangle 1187. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1187
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5997398951, 5823323949, 5656054426, 5495201762, 5340407352, 5191339777, 5047692295, 4909180594, 4775540788, 4646527617, 4521912832, 4401483740, 4285041899, 4172401931, 4063390452, 3957845107, 3855613693, 3756553354, 3660529867, 3567416972, 3477095777, 3389454206, 3304386502, 3221792762, 3141578522, 3063654373, 2987935607, 2914341891, 2842796974, 2773228413, 2705567318, 2639748122, 2575708369, 2513388513, 2452731739, 2393683793, 2336192826, 2280209251, 2225685608, 2172576441, 2120838180, 2070429042, 2021308920, 1973439301, 1926783175, 1881304955, 1836970403, 1793746561, 1751601685, 1710505182, 1670427559, 1631340362, 1593216132, 1556028356, 1519751423, 1484360582, 1449831905, 1416142248, 1383269220, 1351191148, 1319887046, 1289336590, 1259520086, 1230418448, 1202013171, 1174286311, 1147220458, 1120798723, 1095004711, 1069822508, 1045236659, 1021232153, 997794410, 974909258, 952562928, 930742034, 909433559, 888624849, 868303592, 848457816, 829075870, 810146418, 791658427, 773601158, 755964157, 738737245, 721910512, 705474306, 689419226, 673736114, 658416049, 643450341, 628830520, 614548333, 600595738, 586964895, 573648162, 560638091, 547927420, 535509068, 523376133, 511521880, 499939747, 488623329, 477566383, 466762817, 456206691, 445892209, 435813716, 425965696, 416342769, 406939682, 397751311, 388772658, 379998843, 371425105, 363046797, 354859383, 346858437, 339039640, 331398773]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1187).prefactor = (557802209426893/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1187).cutoff/(generalMeanRows 1187).c)).2 =
    (605421298251763/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1187).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1187).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1187).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1187

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1187).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1187).criticalRate j.val*(generalMeanRows 1187).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1187).c*(generalMeanRows 1187).criticalPoint j.val)).2-
      (generalMeanRows 1187).J/2-(generalMeanRows 1187).error (generalMeanGrid j.val)+
      (generalMeanRows 1187).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1187).c)).2-
      (generalMeanRows 1187).J/2-(generalMeanRows 1187).error 4 := by
  have he : (generalMeanRows 1187).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1187) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1187)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1187

/-! Kernel-checked entropy margins for general spectral rectangle 1188. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1188
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6121078386, 5941325763, 5768638493, 5602613401, 5442878389, 5289089513, 5140928384, 4998099845, 4860329899, 4727363843, 4598964604, 4474911228, 4354997528, 4239030861, 4126831021, 4018229236, 3913067259, 3811196543, 3712477494, 3616778781, 3523976720, 3433954702, 3346602676, 3261816670, 3179498364, 3099554685, 3021897445, 2946443005, 2873111967, 2801828891, 2732522032, 2665123104, 2599567052, 2535791854, 2473738327, 2413349955, 2354572728, 2297354987, 2241647293, 2187402291, 2134574596, 2083120681, 2032998769, 1984168744, 1936592056, 1890231643, 1845051847, 1801018347, 1758098088, 1716259219, 1675471033, 1635703911, 1596929274, 1559119527, 1522248020, 1486289002, 1451217579, 1417009679, 1383642015, 1351092052, 1319337971, 1288358646, 1258133611, 1228643032, 1199867685, 1171788931, 1144388692, 1117649431, 1091554131, 1066086273, 1041229824, 1016969210, 993289309, 970175428, 947613292, 925589027, 904089146, 883100539, 862610458, 842606504, 823076617, 804009066, 785392436, 767215619, 749467805, 732138471, 715217374, 698694540, 682560260, 666805076, 651419778, 636395395, 621723189, 607394647, 593401474, 579735588, 566389113, 553354374, 540623890, 528190371, 516046708, 504185974, 492601413, 481286440, 470234633, 459439732, 448895631, 438596375, 428536158, 418709315, 409110322, 399733792, 390574468, 381627223, 372887054, 364349083, 356008547, 347860803, 339901316, 332125666, 324529536]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1188).prefactor = (1154623302861379/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1188).cutoff/(generalMeanRows 1188).c)).2 =
    (300340976443933/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1188).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1188).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1188).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1188

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1188).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1188).criticalRate j.val*(generalMeanRows 1188).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1188).c*(generalMeanRows 1188).criticalPoint j.val)).2-
      (generalMeanRows 1188).J/2-(generalMeanRows 1188).error (generalMeanGrid j.val)+
      (generalMeanRows 1188).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1188).c)).2-
      (generalMeanRows 1188).J/2-(generalMeanRows 1188).error 4 := by
  have he : (generalMeanRows 1188).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1188) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1188)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1188

/-! Kernel-checked entropy margins for general spectral rectangle 1189. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1189
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6606477404, 6419231911, 6239229370, 6066055461, 5899327986, 5738693846, 5583826342, 5434422771, 5290202274, 5150903908, 5016284912, 4886119152, 4760195717, 4638317648, 4520300796, 4405972783, 4295172060, 4187747057, 4083555400, 3982463212, 3884344462, 3789080383, 3696558933, 3606674304, 3519326474, 3434420796, 3351867622, 3271581955, 3193483131, 3117494529, 3043543301, 2971560123, 2901478971, 2833236904, 2766773874, 2702032547, 2638958134, 2577498237, 2517602711, 2459223525, 2402314648, 2346831927, 2292732987, 2239977131, 2188525246, 2138339723, 2089384374, 2041624358, 1995026113, 1949557292, 1905186700, 1861884242, 1819620865, 1778368510, 1738100070, 1698789340, 1660410978, 1622940469, 1586354085, 1550628855, 1515742529, 1481673549, 1448401020, 1415904686, 1384164900, 1353162600, 1322879291, 1293297019, 1264398351, 1236166356, 1208584586, 1181637060, 1155308246, 1129583044, 1104446772, 1079885153, 1055884297, 1032430693, 1009511194, 987113001, 965223661, 943831046, 922923348, 902489069, 882517009, 862996257, 843916186, 825266438, 807036920, 789217797, 771799481, 754772626, 738128121, 721857080, 705950841, 690400956, 675199185, 660337491, 645808035, 631603170, 617715433, 604137546, 590862404, 577883077, 565192799, 552784969, 540653143, 528791033, 517192498, 505851546, 494762326, 483919127, 473316371, 462948613, 452810537, 442896951, 433202785, 423723087, 414453023, 405387870, 396523015]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1189).prefactor = (5975034470015151/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1189).cutoff/(generalMeanRows 1189).c)).2 =
    (307483955067671/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1189).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1189).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1189).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1189

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1189).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1189).criticalRate j.val*(generalMeanRows 1189).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1189).c*(generalMeanRows 1189).criticalPoint j.val)).2-
      (generalMeanRows 1189).J/2-(generalMeanRows 1189).error (generalMeanGrid j.val)+
      (generalMeanRows 1189).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1189).c)).2-
      (generalMeanRows 1189).J/2-(generalMeanRows 1189).error 4 := by
  have he : (generalMeanRows 1189).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1189) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1189)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1189

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock16 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 16 i) := by
  fin_cases i
  · exact EntropyRow1120.numerical
  · exact EntropyRow1121.numerical
  · exact EntropyRow1122.numerical
  · exact EntropyRow1123.numerical
  · exact EntropyRow1124.numerical
  · exact EntropyRow1125.numerical
  · exact EntropyRow1126.numerical
  · exact EntropyRow1127.numerical
  · exact EntropyRow1128.numerical
  · exact EntropyRow1129.numerical
  · exact EntropyRow1130.numerical
  · exact EntropyRow1131.numerical
  · exact EntropyRow1132.numerical
  · exact EntropyRow1133.numerical
  · exact EntropyRow1134.numerical
  · exact EntropyRow1135.numerical
  · exact EntropyRow1136.numerical
  · exact EntropyRow1137.numerical
  · exact EntropyRow1138.numerical
  · exact EntropyRow1139.numerical
  · exact EntropyRow1140.numerical
  · exact EntropyRow1141.numerical
  · exact EntropyRow1142.numerical
  · exact EntropyRow1143.numerical
  · exact EntropyRow1144.numerical
  · exact EntropyRow1145.numerical
  · exact EntropyRow1146.numerical
  · exact EntropyRow1147.numerical
  · exact EntropyRow1148.numerical
  · exact EntropyRow1149.numerical
  · exact EntropyRow1150.numerical
  · exact EntropyRow1151.numerical
  · exact EntropyRow1152.numerical
  · exact EntropyRow1153.numerical
  · exact EntropyRow1154.numerical
  · exact EntropyRow1155.numerical
  · exact EntropyRow1156.numerical
  · exact EntropyRow1157.numerical
  · exact EntropyRow1158.numerical
  · exact EntropyRow1159.numerical
  · exact EntropyRow1160.numerical
  · exact EntropyRow1161.numerical
  · exact EntropyRow1162.numerical
  · exact EntropyRow1163.numerical
  · exact EntropyRow1164.numerical
  · exact EntropyRow1165.numerical
  · exact EntropyRow1166.numerical
  · exact EntropyRow1167.numerical
  · exact EntropyRow1168.numerical
  · exact EntropyRow1169.numerical
  · exact EntropyRow1170.numerical
  · exact EntropyRow1171.numerical
  · exact EntropyRow1172.numerical
  · exact EntropyRow1173.numerical
  · exact EntropyRow1174.numerical
  · exact EntropyRow1175.numerical
  · exact EntropyRow1176.numerical
  · exact EntropyRow1177.numerical
  · exact EntropyRow1178.numerical
  · exact EntropyRow1179.numerical
  · exact EntropyRow1180.numerical
  · exact EntropyRow1181.numerical
  · exact EntropyRow1182.numerical
  · exact EntropyRow1183.numerical
  · exact EntropyRow1184.numerical
  · exact EntropyRow1185.numerical
  · exact EntropyRow1186.numerical
  · exact EntropyRow1187.numerical
  · exact EntropyRow1188.numerical
  · exact EntropyRow1189.numerical
end SingularValueBounds.KL.Certificates
