import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 70. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0070
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5773151420, 5584379588, 5404542897, 5233098640, 5069543620, 4913410704, 4764265736, 4621704773, 4485351606, 4354855514, 4229889248, 4110147195, 3995343718, 3885211645, 3779500893, 3677977207, 3580421018, 3486626384, 3396400028, 3309560452, 3225937123, 3145369717, 3067707433, 2992808350, 2920538838, 2850773014, 2783392232, 2718284617, 2655344631, 2594472666, 2535574675, 2478561816, 2423350133, 2369860254, 2318017105, 2267749652, 2218990654, 2171676437, 2125746676, 2081144200, 2037814806, 1995707079, 1954772235, 1914963965, 1876238294, 1838553444, 1801869710, 1766149344, 1731356441, 1697456838, 1664418016, 1632209006, 1600800308, 1570163804, 1540272690, 1511101397, 1482625529, 1454821796, 1427667959, 1401142769, 1375225921, 1349897997, 1325140424, 1300935428, 1277265994, 1254115826, 1231469309, 1209311477, 1187627978, 1166405042, 1145629454, 1125288528, 1105370074, 1085862382, 1066754192, 1048034675, 1029693412, 1011720376, 994105908, 976840704, 959915800, 943322549, 927052614, 911097950, 895450789, 880103631, 865049231, 850280586, 835790925, 821573701, 807622576, 793931419, 780494290, 767305438, 754359288, 741650438, 729173648, 716923836, 704896069, 693085561, 681487663, 670097860, 658911765, 647925113, 637133759, 626533670, 616120924, 605891704, 595842293, 585969074, 576268522, 566737205, 557371777, 548168978, 539125627, 530238625, 521504946, 512921640, 504485827, 496194696, 488045501]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 70).prefactor = (5290013569953033/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 70).cutoff/(generalMeanRows 70).c)).2 =
    (591713743237/1250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 70).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 70).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 70).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 70

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 70).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 70).criticalRate j.val*(generalMeanRows 70).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 70).c*(generalMeanRows 70).criticalPoint j.val)).2-
      (generalMeanRows 70).J/2-(generalMeanRows 70).error (generalMeanGrid j.val)+
      (generalMeanRows 70).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 70).c)).2-
      (generalMeanRows 70).J/2-(generalMeanRows 70).error 4 := by
  have he : (generalMeanRows 70).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 70) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 70)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0070

/-! Kernel-checked entropy margins for general spectral rectangle 71. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0071
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5198404706, 5007337545, 4825507242, 4652357239, 4487371294, 4330069961, 4180007445, 4036768780, 3899967295, 3769242333, 3644257189, 3524697240, 3410268254, 3300694849, 3195719089, 3095099208, 2998608433, 2906033919, 2817175763, 2731846100, 2649868278, 2571076088, 2495313065, 2422431834, 2352293509, 2284767140, 2219729197, 2157063092, 2096658737, 2038412135, 1982224997, 1928004385, 1875662386, 1825115802, 1776285863, 1729097962, 1683481401, 1639369166, 1596697701, 1555406711, 1515438967, 1476740134, 1439258600, 1402945319, 1367753670, 1333639318, 1300560082, 1268475821, 1237348313, 1207141158, 1177819671, 1149350791, 1121702993, 1094846206, 1068751733, 1043392180, 1018741384, 994774352, 971467198, 948797084, 926742167, 905281549, 884395227, 864064047, 844269665, 824994499, 806221700, 787935108, 770119223, 752759171, 735840671, 719350011, 703274018, 687600031, 672315882, 657409864, 642870720, 628687612, 614850110, 601348167, 588172105, 575312598, 562760656, 550507609, 538545092, 526865037, 515459654, 504321420, 493443071, 482817588, 472438188, 462298312, 452391617, 442711970, 433253433, 424010262, 414976894, 406147941, 397518186, 389082571, 380836197, 372774313, 364892311, 357185723, 349650213, 342281575, 335075725, 328028698, 321136644, 314395823, 307802603, 301353453, 295044941, 288873732, 282836583, 276930338, 271151931, 265498375, 259966767, 254554279, 249258160]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 71).prefactor = (5446307899279137/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 71).cutoff/(generalMeanRows 71).c)).2 =
    (204564362930623/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 71).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 71).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 71).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 71

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 71).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 71).criticalRate j.val*(generalMeanRows 71).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 71).c*(generalMeanRows 71).criticalPoint j.val)).2-
      (generalMeanRows 71).J/2-(generalMeanRows 71).error (generalMeanGrid j.val)+
      (generalMeanRows 71).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 71).c)).2-
      (generalMeanRows 71).J/2-(generalMeanRows 71).error 4 := by
  have he : (generalMeanRows 71).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 71) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 71)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0071

/-! Kernel-checked entropy margins for general spectral rectangle 72. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0072
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4882791147, 4689867650, 4506462624, 4332003498, 4165959036, 4007835726, 3857174561, 3713548148, 3576558112, 3445832759, 3321024965, 3201810263, 3087885106, 2978965297, 2874784543, 2775093154, 2679656838, 2588255606, 2500682768, 2416744005, 2336256522, 2259048267, 2184957205, 2113830655, 2045524677, 1979903499, 1916838990, 1856210173, 1797902774, 1741808795, 1687826130, 1635858195, 1585813594, 1537605801, 1491152867, 1446377148, 1403205045, 1361566768, 1321396112, 1282630248, 1245209528, 1209077305, 1174179755, 1140465725, 1107886576, 1076396048, 1045950121, 1016506897, 988026482, 960470874, 933803863, 907990935, 882999176, 858797194, 835355032, 812644096, 790637083, 769307912, 748631663, 728584518, 709143700, 690287426, 671994851, 654246028, 637021855, 620304038, 604075052, 588318100, 573017080, 558156548, 543721692, 529698295, 516072713, 502831844, 489963104, 477454400, 465294113, 453471072, 441974533, 430794162, 419920015, 409342521, 399052466, 389040974, 379299498, 369819800, 360593940, 351614264, 342873388, 334364193, 326079807, 318013599, 310159168, 302510331, 295061119, 287805762, 280738688, 273854509, 267148016, 260614173, 254248109, 248045110, 242000618, 236110217, 230369636, 224774738, 219321516, 214006089, 208824699, 203773700, 198849563, 194048864, 189368285, 184804608, 180354710, 176015565, 171784235, 167657869, 163633699, 159709042, 155881289]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 72).prefactor = (1121443994103543/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 72).cutoff/(generalMeanRows 72).c)).2 =
    (91410903480377/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 72).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 72).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 72).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 72

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 72).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 72).criticalRate j.val*(generalMeanRows 72).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 72).c*(generalMeanRows 72).criticalPoint j.val)).2-
      (generalMeanRows 72).J/2-(generalMeanRows 72).error (generalMeanGrid j.val)+
      (generalMeanRows 72).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 72).c)).2-
      (generalMeanRows 72).J/2-(generalMeanRows 72).error 4 := by
  have he : (generalMeanRows 72).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 72) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 72)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0072

/-! Kernel-checked entropy margins for general spectral rectangle 73. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0073
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4937614341, 4739878453, 4551941616, 4373214343, 4203149679, 4041239483, 3887011117, 3740024472, 3599869299, 3466162806, 3338547480, 3216689129, 3100275088, 2989012605, 2882627359, 2780862113, 2683475482, 2590240804, 2500945105, 2415388148, 2333381560, 2254748028, 2179320553, 2106941771, 2037463315, 1970745230, 1906655434, 1845069212, 1785868752, 1728942709, 1674185808, 1621498462, 1570786431, 1521960494, 1474936147, 1429633319, 1385976114, 1343892558, 1303314377, 1264176774, 1226418236, 1189980340, 1154807578, 1120847195, 1088049031, 1056365378, 1025750841, 996162214, 967558358, 939900088, 913150069, 887272712, 862234086, 838001827, 814545055, 791834297, 769841411, 748539520, 727902945, 707907144, 688528653, 669745032, 651534815, 633877456, 616753290, 600143484, 584029997, 568395545, 553223558, 538498151, 524204088, 510326752, 496852114, 483766708, 471057602, 458712376, 446719095, 435066289, 423742929, 412738410, 402042533, 391645481, 381537806, 371710414, 362154545, 352861764, 343823939, 335033238, 326482107, 318163262, 310069681, 302194586, 294531437, 287073922, 279815948, 272751628, 265875280, 259181410, 252664713, 246320059, 240142488, 234127205, 228269572, 222565104, 217009457, 211598432, 206327961, 201194107, 196193057, 191321119, 186574716, 181950383, 177444760, 173054594, 168776729, 164608105, 160545757, 156586807, 152728465, 148968025, 145302858]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 73).prefactor = (721610776952541/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 73).cutoff/(generalMeanRows 73).c)).2 =
    (71433797386107/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 73).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 73).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 73).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 73

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 73).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 73).criticalRate j.val*(generalMeanRows 73).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 73).c*(generalMeanRows 73).criticalPoint j.val)).2-
      (generalMeanRows 73).J/2-(generalMeanRows 73).error (generalMeanGrid j.val)+
      (generalMeanRows 73).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 73).c)).2-
      (generalMeanRows 73).J/2-(generalMeanRows 73).error 4 := by
  have he : (generalMeanRows 73).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 73) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 73)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0073

/-! Kernel-checked entropy margins for general spectral rectangle 74. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0074
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5270031080, 5064659152, 4869376247, 4683575430, 4506693614, 4338207725, 4177631284, 4024511347, 3878425745, 3738980609, 3605808124, 3478564505, 3356928155, 3240597992, 3129291923, 3022745458, 2920710435, 2822953857, 2729256824, 2639413554, 2553230482, 2470525426, 2391126826, 2314873037, 2241611673, 2171199008, 2103499411, 2038384833, 1975734325, 1915433589, 1857374565, 1801455047, 1747578319, 1695652828, 1645591864, 1597313275, 1550739194, 1505795786, 1462413011, 1420524403, 1380066861, 1340980459, 1303208263, 1266696160, 1231392699, 1197248944, 1164218332, 1132256540, 1101321366, 1071372608, 1042371962, 1014282910, 987070632, 960701913, 935145057, 910369805, 886347265, 863049835, 840451140, 818525967, 797250205, 776600792, 756555658, 737093675, 718194615, 699839101, 682008563, 664685205, 647851961, 631492463, 615591006, 600132516, 585102522, 570487124, 556272969, 542447227, 528997560, 515912108, 503179459, 490788634, 478729067, 466990583, 455563385, 444438034, 433605434, 423056818, 412783732, 402778025, 393031831, 383537561, 374287890, 365275744, 356494293, 347936939, 339597306, 331469233, 323546762, 315824135, 308295779, 300956305, 293800499, 286823313, 280019859, 273385408, 266915376, 260605323, 254450950, 248448087, 242592695, 236880856, 231308772, 225872758, 220569241, 215394754, 210345933, 205419511, 200612318, 195921278, 191343400, 186875782, 182515605]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 74).prefactor = (5943447097443231/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 74).cutoff/(generalMeanRows 74).c)).2 =
    (187095337249983/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 74).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 74).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 74).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 74

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 74).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 74).criticalRate j.val*(generalMeanRows 74).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 74).c*(generalMeanRows 74).criticalPoint j.val)).2-
      (generalMeanRows 74).J/2-(generalMeanRows 74).error (generalMeanGrid j.val)+
      (generalMeanRows 74).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 74).c)).2-
      (generalMeanRows 74).J/2-(generalMeanRows 74).error 4 := by
  have he : (generalMeanRows 74).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 74) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 74)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0074

/-! Kernel-checked entropy margins for general spectral rectangle 75. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0075
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5524846679, 5340006648, 5164008196, 4996306173, 4836395663, 4683808452, 4538109878, 4398895996, 4265791039, 4138445124, 4016532175, 3899748051, 3787808840, 3680449311, 3577421500, 3478493428, 3383447919, 3292081526, 3204203540, 3119635088, 3038208296, 2959765526, 2884158664, 2811248475, 2740903999, 2673001992, 2607426417, 2544067966, 2482823619, 2423596234, 2366294169, 2310830932, 2257124847, 2205098756, 2154679732, 2105798818, 2058390777, 2012393870, 1967749634, 1924402688, 1882300548, 1841393448, 1801634184, 1762977956, 1725382232, 1688806610, 1653212699, 1618563998, 1584825790, 1551965038, 1519950291, 1488751594, 1458340402, 1428689505, 1399772950, 1371565972, 1344044931, 1317187249, 1290971353, 1265376619, 1240383326, 1215972599, 1192126376, 1168827353, 1146058955, 1123805291, 1102051122, 1080781827, 1059983370, 1039642275, 1019745591, 1000280873, 981236151, 962599912, 944361072, 926508961, 909033300, 891924181, 875172054, 858767706, 842702248, 826967098, 811553969, 796454854, 781662015, 767167969, 752965479, 739047542, 725407379, 712038426, 698934322, 686088906, 673496204, 661150421, 649045940, 637177305, 625539224, 614126556, 602934307, 591957627, 581191800, 570632241, 560274494, 550114220, 540147201, 530369328, 520776604, 511365134, 502131125, 493070883, 484180806, 475457383, 466897192, 458496897, 450253240, 442163046, 434223217, 426430726, 418782623, 411276022, 403908111]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 75).prefactor = (1352839605727059/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 75).cutoff/(generalMeanRows 75).c)).2 =
    (478121597348197/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 75).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 75).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 75).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 75

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 75).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 75).criticalRate j.val*(generalMeanRows 75).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 75).c*(generalMeanRows 75).criticalPoint j.val)).2-
      (generalMeanRows 75).J/2-(generalMeanRows 75).error (generalMeanGrid j.val)+
      (generalMeanRows 75).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 75).c)).2-
      (generalMeanRows 75).J/2-(generalMeanRows 75).error 4 := by
  have he : (generalMeanRows 75).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 75) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 75)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0075

/-! Kernel-checked entropy margins for general spectral rectangle 76. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0076
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8277378047, 8027126245, 7787859584, 7558965701, 7339874863, 7130056176, 6929014223, 6736286076, 6551438614, 6374066132, 6203788183, 6040247635, 5883108916, 5732056423, 5586793078, 5447039008, 5312530347, 5183018143, 5058267343, 4938055879, 4822173819, 4710422579, 4602614213, 4498570740, 4398123532, 4301112743, 4207386780, 4116801814, 4029221320, 3944515655, 3862561662, 3783242297, 3706446289, 3632067815, 3560006198, 3490165626, 3422454886, 3356787118, 3293079581, 3231253433, 3171233530, 3112948225, 3056329196, 3001311265, 2947832245, 2895832781, 2845256213, 2796048436, 2748157772, 2701534854, 2656132508, 2611905645, 2568811160, 2526807839, 2485856259, 2445918712, 2406959114, 2368942933, 2331837112, 2295610004, 2260231299, 2225671967, 2191904194, 2158901330, 2126637831, 2095089210, 2064231988, 2034043649, 2004502595, 1975588102, 1947280286, 1919560061, 1892409103, 1865809820, 1839745313, 1814199352, 1789156341, 1764601293, 1740519800, 1716898015, 1693722617, 1670980797, 1648660231, 1626749060, 1605235872, 1584109679, 1563359902, 1542976353, 1522949218, 1503269039, 1483926702, 1464913424, 1446220732, 1427840459, 1409764723, 1391985923, 1374496720, 1357290032, 1340359019, 1323697077, 1307297825, 1291155098, 1275262938, 1259615586, 1244207471, 1229033206, 1214087580, 1199365550, 1184862235, 1170572908, 1156492992, 1142618056, 1128943802, 1115466068, 1102180819, 1089084141, 1076172238, 1063441429, 1050888140, 1038508902, 1026300349]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 76).prefactor = (2852050798999563/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 76).cutoff/(generalMeanRows 76).c)).2 =
    (21164123664967/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 76).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 76).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 76).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 76

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 76).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 76).criticalRate j.val*(generalMeanRows 76).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 76).c*(generalMeanRows 76).criticalPoint j.val)).2-
      (generalMeanRows 76).J/2-(generalMeanRows 76).error (generalMeanGrid j.val)+
      (generalMeanRows 76).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 76).c)).2-
      (generalMeanRows 76).J/2-(generalMeanRows 76).error 4 := by
  have he : (generalMeanRows 76).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 76) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 76)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0076

/-! Kernel-checked entropy margins for general spectral rectangle 77. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0077
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7920479184, 7658060071, 7407208073, 7167282268, 6937686342, 6717864608, 6507298492, 6305503390, 6112025868, 5926441150, 5748350858, 5577380981, 5413180035, 5255417394, 5103781783, 4957979897, 4817735147, 4682786511, 4552887483, 4427805110, 4307319104, 4191221026, 4079313536, 3971409693, 3867332318, 3766913396, 3669993525, 3576421401, 3486053347, 3398752864, 3314390221, 3232842071, 3153991088, 3077725634, 3003939443, 2932531327, 2863404903, 2796468329, 2731634068, 2668818657, 2607942491, 2548929627, 2491707590, 2436207198, 2382362393, 2330110080, 2279389984, 2230144503, 2182318579, 2135859571, 2090717134, 2046843113, 2004191429, 1962717987, 1922380574, 1883138772, 1844953872, 1807788794, 1771608012, 1736377476, 1702064550, 1668637939, 1636067635, 1604324853, 1573381974, 1543212497, 1513790984, 1485093013, 1457095134, 1429774824, 1403110445, 1377081208, 1351667130, 1326849004, 1302608362, 1278927445, 1255789168, 1233177096, 1211075412, 1189468891, 1168342878, 1147683260, 1127476444, 1107709335, 1088369316, 1069444226, 1050922345, 1032792369, 1015043399, 997664921, 980646791, 963979220, 947652758, 931658284, 915986987, 900630360, 885580181, 870828509, 856367665, 842190228, 828289021, 814657103, 801287759, 788174493, 775311017, 762691243, 750309279, 738159417, 726236127, 714534054, 703048005, 691772948, 680704006, 669836445, 659165679, 648687253, 638396848, 628290270, 618363448, 608612429, 599033374]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 77).prefactor = (6013474155145631/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 77).cutoff/(generalMeanRows 77).c)).2 =
    (2838940091549/7812500000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 77).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 77).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 77).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 77

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 77).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 77).criticalRate j.val*(generalMeanRows 77).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 77).c*(generalMeanRows 77).criticalPoint j.val)).2-
      (generalMeanRows 77).J/2-(generalMeanRows 77).error (generalMeanGrid j.val)+
      (generalMeanRows 77).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 77).c)).2-
      (generalMeanRows 77).J/2-(generalMeanRows 77).error 4 := by
  have he : (generalMeanRows 77).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 77) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 77)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0077

/-! Kernel-checked entropy margins for general spectral rectangle 78. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0078
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6879439807, 6670793298, 6471544759, 6281154343, 6099120155, 5924974926, 5758283053, 5598637954, 5445659703, 5298992896, 5158304736, 5023283295, 4893635952, 4769087957, 4649381142, 4534272734, 4423534274, 4316950629, 4214319084, 4115448506, 4020158581, 3928279103, 3839649325, 3754117354, 3671539591, 3591780222, 3514710728, 3440209448, 3368161160, 3298456701, 3230992601, 3165670754, 3102398106, 3041086360, 2981651705, 2924014562, 2868099345, 2813834237, 2761150979, 2709984679, 2660273621, 2611959093, 2564985230, 2519298854, 2474849332, 2431588445, 2389470252, 2348450980, 2308488902, 2269544234, 2231579036, 2194557115, 2158443935, 2123206532, 2088813437, 2055234599, 2022441311, 1990406145, 1959102891, 1928506489, 1898592980, 1869339448, 1840723966, 1812725553, 1785324127, 1758500458, 1732236130, 1706513499, 1681315660, 1656626409, 1632430209, 1608712162, 1585457975, 1562653932, 1540286870, 1518344151, 1496813636, 1475683667, 1454943040, 1434580984, 1414587147, 1394951569, 1375664672, 1356717235, 1338100385, 1319805576, 1301824579, 1284149464, 1266772588, 1249686585, 1232884348, 1216359024, 1200104001, 1184112893, 1168379538, 1152897982, 1137662473, 1122667454, 1107907549, 1093377563, 1079072467, 1064987397, 1051117644, 1037458649, 1024005995, 1010755404, 997702728, 984843947, 972175162, 959692590, 947392560, 935271510, 923325981, 911552610, 899948135, 888509381, 877233264, 866116783, 855157021, 844351138, 833696371]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 78).prefactor = (205442269850663/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 78).cutoff/(generalMeanRows 78).c)).2 =
    (225726675133017/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 78).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 78).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 78).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 78

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 78).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 78).criticalRate j.val*(generalMeanRows 78).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 78).c*(generalMeanRows 78).criticalPoint j.val)).2-
      (generalMeanRows 78).J/2-(generalMeanRows 78).error (generalMeanGrid j.val)+
      (generalMeanRows 78).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 78).c)).2-
      (generalMeanRows 78).J/2-(generalMeanRows 78).error 4 := by
  have he : (generalMeanRows 78).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 78) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 78)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0078

/-! Kernel-checked entropy margins for general spectral rectangle 79. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0079
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7024735179, 6807471053, 6599996176, 6401749150, 6212208036, 6030886893, 5857332704, 5691122621, 5531861506, 5379179713, 5232731095, 5092191201, 4957255643, 4827638615, 4703071540, 4583301846, 4468091836, 4357217664, 4250468390, 4147645112, 4048560169, 3953036410, 3860906509, 3772012345, 3686204419, 3603341315, 3523289207, 3445921391, 3371117859, 3298764895, 3228754706, 3160985071, 3095359018, 3031784523, 2970174223, 2910445157, 2852518510, 2796319389, 2741776600, 2688822445, 2637392533, 2587425596, 2538863323, 2491650200, 2445733362, 2401062447, 2357589471, 2315268700, 2274056530, 2233911379, 2194793582, 2156665292, 2119490389, 2083234387, 2047864357, 2013348843, 1979657793, 1946762486, 1914635465, 1883250476, 1852582409, 1822607241, 1793301981, 1764644624, 1736614097, 1709190222, 1682353664, 1656085899, 1630369168, 1605186447, 1580521407, 1556358385, 1532682348, 1509478871, 1486734102, 1464434737, 1442567996, 1421121599, 1400083742, 1379443074, 1359188681, 1339310061, 1319797107, 1300640093, 1281829649, 1263356755, 1245212718, 1227389159, 1209878002, 1192671458, 1175762014, 1159142421, 1142805680, 1126745036, 1110953962, 1095426155, 1080155522, 1065136173, 1050362413, 1035828733, 1021529801, 1007460459, 993615711, 979990718, 966580793, 953381395, 940388120, 927596698, 915002988, 902602970, 890392746, 878368529, 866526641, 854863510, 843375666, 832059734, 820912434, 809930576, 799111056, 788450853, 777947028]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 79).prefactor = (534903085925393/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 79).cutoff/(generalMeanRows 79).c)).2 =
    (220201757039727/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 79).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 79).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 79).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 79

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 79).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 79).criticalRate j.val*(generalMeanRows 79).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 79).c*(generalMeanRows 79).criticalPoint j.val)).2-
      (generalMeanRows 79).J/2-(generalMeanRows 79).error (generalMeanGrid j.val)+
      (generalMeanRows 79).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 79).c)).2-
      (generalMeanRows 79).J/2-(generalMeanRows 79).error 4 := by
  have he : (generalMeanRows 79).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 79) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 79)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0079

/-! Kernel-checked entropy margins for general spectral rectangle 80. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0080
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7174343175, 6948198413, 6732250800, 6525916453, 6328652518, 6139953574, 5959348425, 5786397249, 5620689027, 5461839244, 5309487816, 5163297213, 5022950759, 4888151096, 4758618777, 4634090990, 4514320385, 4399074011, 4288132330, 4181288318, 4078346636, 3979122867, 3883442808, 3791141824, 3702064241, 3616062788, 3532998082, 3452738145, 3375157957, 3300139041, 3227569074, 3157341530, 3089355336, 3023514564, 2959728134, 2897909539, 2837976586, 2779851158, 2723458985, 2668729435, 2615595311, 2563992668, 2513860633, 2465141244, 2417779295, 2371722185, 2326919785, 2283324306, 2240890179, 2199573938, 2159334111, 2120131120, 2081927183, 2044686221, 2008373774, 1972956919, 1938404193, 1904685520, 1871772140, 1839636549, 1808252432, 1777594607, 1747638971, 1718362446, 1689742927, 1661759241, 1634391096, 1607619046, 1581424442, 1555789401, 1530696770, 1506130085, 1482073548, 1458511987, 1435430833, 1412816092, 1390654314, 1368932572, 1347638438, 1326759959, 1306285635, 1286204400, 1266505603, 1247178987, 1228214674, 1209603147, 1191335233, 1173402093, 1155795198, 1138506326, 1121527542, 1104851186, 1088469866, 1072376441, 1056564012, 1041025915, 1025755706, 1010747155, 995994238, 981491124, 967232172, 953211920, 939425081, 925866530, 912531306, 899414596, 886511736, 873818204, 861329611, 849041700, 836950336, 825051508, 813341319, 801815981, 790471816, 779305248, 768312798, 757491086, 746836821, 736346801, 726017910]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 80).prefactor = (5570836255664259/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 80).cutoff/(generalMeanRows 80).c)).2 =
    (429474443547261/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 80).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 80).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 80).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 80

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 80).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 80).criticalRate j.val*(generalMeanRows 80).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 80).c*(generalMeanRows 80).criticalPoint j.val)).2-
      (generalMeanRows 80).J/2-(generalMeanRows 80).error (generalMeanGrid j.val)+
      (generalMeanRows 80).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 80).c)).2-
      (generalMeanRows 80).J/2-(generalMeanRows 80).error 4 := by
  have he : (generalMeanRows 80).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 80) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 80)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0080

/-! Kernel-checked entropy margins for general spectral rectangle 81. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0081
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6094604441, 5865543931, 5647114907, 5438714141, 5239780597, 5049791729, 4868260179, 4694730838, 4528778205, 4370004019, 4218035124, 4072521545, 3933134737, 3799566007, 3671525068, 3548738731, 3430949701, 3317915480, 3209407362, 3105209511, 3005118105, 2908940559, 2816494800, 2727608599, 2642118955, 2559871522, 2480720083, 2404526049, 2331158011, 2260491308, 2192407632, 2126794661, 2063545710, 2002559413, 1943739418, 1886994109, 1832236342, 1779383194, 1728355737, 1679078820, 1631480862, 1585493662, 1541052221, 1498094573, 1456561622, 1416396997, 1377546907, 1339960011, 1303587291, 1268381937, 1234299229, 1201296438, 1169332725, 1138369046, 1108368063, 1079294062, 1051112872, 1023791792, 997299516, 971606072, 946682750, 922502051, 899037623, 876264208, 854157594, 832694563, 811852845, 791611075, 771948753, 752846201, 734284527, 716245590, 698711967, 681666917, 665094355, 648978820, 633305447, 618059943, 603228562, 588798076, 574755760, 561089365, 547787100, 534837609, 522229958, 509953612, 497998422, 486354604, 475012729, 463963705, 453198764, 442709449, 432487600, 422525342, 412815077, 403349467, 394121426, 385124114, 376350919, 367795456, 359451552, 351313243, 343374759, 335630525, 328075146, 320703405, 313510251, 306490800, 299640323, 292954240, 286428120, 280057667, 273838725, 267767262, 261839375, 256051281, 250399310, 244879906, 239489621, 234225111, 229083130]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 81).prefactor = (2900919568797547/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 81).cutoff/(generalMeanRows 81).c)).2 =
    (158267016183333/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 81).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 81).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 81).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 81

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 81).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 81).criticalRate j.val*(generalMeanRows 81).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 81).c*(generalMeanRows 81).criticalPoint j.val)).2-
      (generalMeanRows 81).J/2-(generalMeanRows 81).error (generalMeanGrid j.val)+
      (generalMeanRows 81).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 81).c)).2-
      (generalMeanRows 81).J/2-(generalMeanRows 81).error 4 := by
  have he : (generalMeanRows 81).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 81) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 81)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0081

/-! Kernel-checked entropy margins for general spectral rectangle 82. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0082
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5857650200, 5679673506, 5509907191, 5347860990, 5193079898, 5045141091, 4903651183, 4768243773, 4638577236, 4514332736, 4395212428, 4280937839, 4171248388, 4065900050, 3964664134, 3867326168, 3773684880, 3683551264, 3596747727, 3513107297, 3432472904, 3354696710, 3279639494, 3207170085, 3137164837, 3069507137, 3004086963, 2940800457, 2879549543, 2820241563, 2762788943, 2707108878, 2653123046, 2600757330, 2549941572, 2500609330, 2452697663, 2406146921, 2360900555, 2316904934, 2274109177, 2232464997, 2191926548, 2152450291, 2113994860, 2076520942, 2039991159, 2004369964, 1969623538, 1935719693, 1902627787, 1870318633, 1838764426, 1807938666, 1777816087, 1748372592, 1719585190, 1691431938, 1663891885, 1636945022, 1610572228, 1584755229, 1559476552, 1534719481, 1510468024, 1486706870, 1463421360, 1440597447, 1418221672, 1396281133, 1374763453, 1353656759, 1332949654, 1312631195, 1292690872, 1273118582, 1253904617, 1235039638, 1216514661, 1198321039, 1180450446, 1162894864, 1145646564, 1128698097, 1112042281, 1095672183, 1079581115, 1063762619, 1048210458, 1032918602, 1017881227, 1003092697, 988547562, 974240547, 960166546, 946320612, 932697953, 919293926, 906104027, 893123887, 880349270, 867776061, 855400267, 843218007, 831225513, 819419119, 807795264, 796350482, 785081401, 773984741, 763057306, 752295984, 741697746, 731259637, 720978778, 710852361, 700877647, 691051967, 681372712, 671837337, 662443357]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 82).prefactor = (4798156056469697/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 82).cutoff/(generalMeanRows 82).c)).2 =
    (242677450970859/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 82).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 82).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 82).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 82

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 82).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 82).criticalRate j.val*(generalMeanRows 82).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 82).c*(generalMeanRows 82).criticalPoint j.val)).2-
      (generalMeanRows 82).J/2-(generalMeanRows 82).error (generalMeanGrid j.val)+
      (generalMeanRows 82).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 82).c)).2-
      (generalMeanRows 82).J/2-(generalMeanRows 82).error 4 := by
  have he : (generalMeanRows 82).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 82) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 82)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0082

/-! Kernel-checked entropy margins for general spectral rectangle 83. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0083
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5925290389, 5741756137, 5566697501, 5399609327, 5240022768, 5087502120, 4941641995, 4802064792, 4668418424, 4540374268, 4417625320, 4299884521, 4186883235, 4078369877, 3974108646, 3873878387, 3777471534, 3684693154, 3595360061, 3509300013, 3426350957, 3346360352, 3269184528, 3194688105, 3122743453, 3053230185, 2986034702, 2921049753, 2858174043, 2797311858, 2738372719, 2681271062, 2625925940, 2572260738, 2520202921, 2469683783, 2420638224, 2373004538, 2326724212, 2281741745, 2238004467, 2195462382, 2154068015, 2113776264, 2074544273, 2036331300, 1999098601, 1962809320, 1927428384, 1892922404, 1859259583, 1826409632, 1794343682, 1763034217, 1732454991, 1702580969, 1673388257, 1644854043, 1616956541, 1589674939, 1562989343, 1536880734, 1511330922, 1486322501, 1461838812, 1437863903, 1414382495, 1391379946, 1368842220, 1346755857, 1325107944, 1303886090, 1283078396, 1262673435, 1242660229, 1223028223, 1203767269, 1184867607, 1166319841, 1148114929, 1130244161, 1112699146, 1095471796, 1078554313, 1061939175, 1045619125, 1029587154, 1013836499, 998360621, 983153204, 968208141, 953519524, 939081638, 924888952, 910936111, 897217925, 883729369, 870465569, 857421802, 844593483, 831976167, 819565537, 807357400, 795347686, 783532438, 771907812, 760470068, 749215571, 738140781, 727242257, 716516645, 705960683, 695571189, 685345065, 675279292, 665370925, 655617093, 646014995, 636561897, 627255133, 618092098]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 83).prefactor = (2474731868759581/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 83).cutoff/(generalMeanRows 83).c)).2 =
    (59443862730637/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 83).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 83).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 83).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 83

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 83).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 83).criticalRate j.val*(generalMeanRows 83).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 83).c*(generalMeanRows 83).criticalPoint j.val)).2-
      (generalMeanRows 83).J/2-(generalMeanRows 83).error (generalMeanGrid j.val)+
      (generalMeanRows 83).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 83).c)).2-
      (generalMeanRows 83).J/2-(generalMeanRows 83).error 4 := by
  have he : (generalMeanRows 83).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 83) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 83)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0083

/-! Kernel-checked entropy margins for general spectral rectangle 84. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0084
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5994505516, 5805309855, 5624863602, 5452646204, 5288174500, 5130999464, 4980703292, 4836896793, 4699217055, 4567325327, 4440905125, 4319660501, 4203314481, 4091607648, 3984296843, 3881153985, 3781964991, 3686528784, 3594656389, 3506170097, 3420902695, 3338696765, 3259404026, 3182884736, 3109007132, 3037646917, 2968686779, 2902015953, 2837529802, 2775129443, 2714721385, 2656217202, 2599533223, 2544590245, 2491313265, 2439631227, 2389476796, 2340786130, 2293498681, 2247557005, 2202906580, 2159495638, 2117275010, 2076197980, 2036220143, 1997299276, 1959395222, 1922469766, 1886486536, 1851410899, 1817209864, 1783851996, 1751307331, 1719547296, 1688544636, 1658273341, 1628708585, 1599826660, 1571604916, 1544021710, 1517056351, 1490689052, 1464900882, 1439673725, 1414990233, 1390833795, 1367188494, 1344039072, 1321370903, 1299169953, 1277422759, 1256116396, 1235238451, 1214777002, 1194720589, 1175058195, 1155779224, 1136873481, 1118331154, 1100142795, 1082299301, 1064791904, 1047612147, 1030751879, 1014203234, 997958620, 982010709, 966352423, 950976922, 935877596, 921048054, 906482113, 892173792, 878117301, 864307031, 850737553, 837403603, 824300080, 811422038, 798764677, 786323341, 774093512, 762070800, 750250942, 738629799, 727203343, 715967662, 704918950, 694053503, 683367718, 672858089, 662521199, 652353723, 642352420, 632514131, 622835779, 613314361, 603946951, 594730691, 585662796, 576740546]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 84).prefactor = (127638570946363/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 84).cutoff/(generalMeanRows 84).c)).2 =
    (58230260964767/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 84).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 84).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 84).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 84

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 84).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 84).criticalRate j.val*(generalMeanRows 84).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 84).c*(generalMeanRows 84).criticalPoint j.val)).2-
      (generalMeanRows 84).J/2-(generalMeanRows 84).error (generalMeanGrid j.val)+
      (generalMeanRows 84).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 84).c)).2-
      (generalMeanRows 84).J/2-(generalMeanRows 84).error 4 := by
  have he : (generalMeanRows 84).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 84) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 84)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0084

/-! Kernel-checked entropy margins for general spectral rectangle 85. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0085
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5518361399, 5325291507, 5141282536, 4965799710, 4798346518, 4638461379, 4485714659, 4339706005, 4200061947, 4066433740, 3938495421, 3815942038, 3698488061, 3585865918, 3477824683, 3374128856, 3274557269, 3178902069, 3086967793, 2998570515, 2913537062, 2831704292, 2752918431, 2677034452, 2603915513, 2533432425, 2465463170, 2399892441, 2336611232, 2275516437, 2216510496, 2159501053, 2104400641, 2051126391, 1999599755, 1949746256, 1901495242, 1854779669, 1809535891, 1765703463, 1723224958, 1682045800, 1642114099, 1603380501, 1565798050, 1529322052, 1493909952, 1459521215, 1426117222, 1393661160, 1362117927, 1331454043, 1301637559, 1272637983, 1244426195, 1216974383, 1190255970, 1164245553, 1138918841, 1114252598, 1090224592, 1066813541, 1043999067, 1021761651, 1000082587, 978943948, 958328542, 938219880, 918602137, 899460127, 880779264, 862545542, 844745499, 827366198, 810395198, 793820535, 777630694, 761814594, 746361566, 731261332, 716503993, 702080004, 687980165, 674195604, 660717760, 647538371, 634649463, 622043334, 609712545, 597649907, 585848472, 574301521, 563002557, 551945294, 541123648, 530531729, 520163835, 510014442, 500078198, 490349918, 480824572, 471497285, 462363329, 453418114, 444657188, 436076230, 427671042, 419437548, 411371789, 403469918, 395728196, 388142988, 380710758, 373428071, 366291581, 359298036, 352444268, 345727196, 339143817, 332691211, 326366531]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 85).prefactor = (2633271911012429/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 85).cutoff/(generalMeanRows 85).c)).2 =
    (81897830233401/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 85).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 85).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 85).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 85

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 85).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 85).criticalRate j.val*(generalMeanRows 85).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 85).c*(generalMeanRows 85).criticalPoint j.val)).2-
      (generalMeanRows 85).J/2-(generalMeanRows 85).error (generalMeanGrid j.val)+
      (generalMeanRows 85).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 85).c)).2-
      (generalMeanRows 85).J/2-(generalMeanRows 85).error 4 := by
  have he : (generalMeanRows 85).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 85) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 85)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0085

/-! Kernel-checked entropy margins for general spectral rectangle 86. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0086
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5497549636, 5322577611, 5155774075, 4996644767, 4844731397, 4699608508, 4560880663, 4428179937, 4301163643, 4179512306, 4062927810, 3951131739, 3843863857, 3740880737, 3641954504, 3546871693, 3455432199, 3367448325, 3282743897, 3201153463, 3122521544, 3046701959, 2973557187, 2902957791, 2834781878, 2768914602, 2705247706, 2643679092, 2584112428, 2526456782, 2470626276, 2416539774, 2364120585, 2313296185, 2263997968, 2216160999, 2169723800, 2124628134, 2080818817, 2038243534, 1996852668, 1956599145, 1917438285, 1879327660, 1842226965, 1806097901, 1770904053, 1736610788, 1703185152, 1670595780, 1638812801, 1607807759, 1577553535, 1548024270, 1519195303, 1491043097, 1463545186, 1436680114, 1410427379, 1384767388, 1359681402, 1335151497, 1311160518, 1287692040, 1264730331, 1242260315, 1220267538, 1198738140, 1177658820, 1157016811, 1136799855, 1116996171, 1097594440, 1078583778, 1059953712, 1041694167, 1023795441, 1006248191, 989043413, 972172429, 955626868, 939398656, 923480001, 907863376, 892541515, 877507392, 862754220, 848275431, 834064674, 820115799, 806422856, 792980078, 779781880, 766822847, 754097729, 741601434, 729329022, 717275695, 705436798, 693807808, 682384329, 671162091, 660136941, 649304840, 638661859, 628204175, 617928067, 607829909, 597906174, 588153421, 578568300, 569147544, 559887970, 550786469, 541840013, 533045645, 524400478, 515901697, 507546551, 499332354, 491256481]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 86).prefactor = (4922238967174953/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 86).cutoff/(generalMeanRows 86).c)).2 =
    (95696404530791/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 86).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 86).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 86).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 86

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 86).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 86).criticalRate j.val*(generalMeanRows 86).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 86).c*(generalMeanRows 86).criticalPoint j.val)).2-
      (generalMeanRows 86).J/2-(generalMeanRows 86).error (generalMeanGrid j.val)+
      (generalMeanRows 86).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 86).c)).2-
      (generalMeanRows 86).J/2-(generalMeanRows 86).error 4 := by
  have he : (generalMeanRows 86).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 86) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 86)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0086

/-! Kernel-checked entropy margins for general spectral rectangle 87. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0087
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5545134964, 5365459443, 5194190631, 5030820691, 4874878719, 4725927519, 4583560717, 4447400185, 4317093708, 4192312899, 4072751305, 3958122694, 3848159504, 3742611428, 3641244129, 3543838063, 3450187408, 3360099076, 3273391819, 3189895393, 3109449799, 3031904585, 2957118193, 2884957367, 2815296601, 2748017627, 2683008942, 2620165377, 2559387680, 2500582150, 2443660279, 2388538432, 2335137541, 2283382822, 2233203515, 2184532641, 2137306765, 2091465793, 2046952765, 2003713674, 1961697288, 1920854992, 1881140629, 1842510364, 1804922548, 1768337590, 1732717845, 1698027500, 1664232473, 1631300313, 1599200114, 1567902426, 1537379174, 1507603587, 1478550124, 1450194406, 1422513156, 1395484141, 1369086112, 1343298757, 1318102646, 1293479191, 1269410597, 1245879824, 1222870547, 1200367120, 1178354540, 1156818417, 1135744940, 1115120851, 1094933417, 1075170402, 1055820043, 1036871032, 1018312487, 1000133936, 982325293, 964876848, 947779240, 931023445, 914600762, 898502794, 882721439, 867248871, 852077532, 837200118, 822609570, 808299057, 794261976, 780491933, 766982738, 753728398, 740723104, 727961228, 715437312, 703146064, 691082349, 679241182, 667617725, 656207280, 645005282, 634007294, 623209005, 612606221, 602194866, 591970970, 581930672, 572070214, 562385935, 552874269, 543531744, 534354974, 525340660, 516485585, 507786612, 499240680, 490844804, 482596069, 474491632, 466528716, 458704609]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 87).prefactor = (1012192877998879/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 87).cutoff/(generalMeanRows 87).c)).2 =
    (469391050952703/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 87).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 87).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 87).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 87

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 87).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 87).criticalRate j.val*(generalMeanRows 87).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 87).c*(generalMeanRows 87).criticalPoint j.val)).2-
      (generalMeanRows 87).J/2-(generalMeanRows 87).error (generalMeanGrid j.val)+
      (generalMeanRows 87).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 87).c)).2-
      (generalMeanRows 87).J/2-(generalMeanRows 87).error 4 := by
  have he : (generalMeanRows 87).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 87) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 87)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0087

/-! Kernel-checked entropy margins for general spectral rectangle 88. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0088
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5094325518, 4912083631, 4738526518, 4573133300, 4415420802, 4264940261, 4121274381, 3984034701, 3852859219, 3727410263, 3607372557, 3492451479, 3382371473, 3276874611, 3175719282, 3078678991, 2985541267, 2896106662, 2810187829, 2727608678, 2648203604, 2571816769, 2498301444, 2427519399, 2359340345, 2293641413, 2230306672, 2169226682, 2110298083, 2053423211, 1998509737, 1945470342, 1894222402, 1844687705, 1796792180, 1750465651, 1705641599, 1662256949, 1620251864, 1579569556, 1540156108, 1501960309, 1464933497, 1429029414, 1394204070, 1360415614, 1327624214, 1295791946, 1264882687, 1234862016, 1205697121, 1177356712, 1149810937, 1123031306, 1096990621, 1071662901, 1047023323, 1023048159, 999714719, 977001299, 954887128, 933352321, 912377833, 891945420, 872037593, 852637587, 833729317, 815297354, 797326885, 779803686, 762714094, 746044980, 729783721, 713918180, 698436681, 683327986, 668581277, 654186137, 640132528, 626410780, 613011567, 599925898, 587145097, 574660793, 562464905, 550549630, 538907429, 527531018, 516413357, 505547639, 494927280, 484545910, 474397365, 464475677, 454775068, 445289941, 436014874, 426944610, 418074056, 409398272, 400912466, 392611989, 384492331, 376549114, 368778085, 361175118, 353736202, 346457442, 339335051, 332365349, 325544759, 318869802, 312337094, 305943344, 299685349, 293559992, 287564239, 281695137, 275949810, 270325457, 264819350]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 88).prefactor = (1300899891675299/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 88).cutoff/(generalMeanRows 88).c)).2 =
    (104128824726189/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 88).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 88).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 88).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 88

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 88).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 88).criticalRate j.val*(generalMeanRows 88).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 88).c*(generalMeanRows 88).criticalPoint j.val)).2-
      (generalMeanRows 88).J/2-(generalMeanRows 88).error (generalMeanGrid j.val)+
      (generalMeanRows 88).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 88).c)).2-
      (generalMeanRows 88).J/2-(generalMeanRows 88).error 4 := by
  have he : (generalMeanRows 88).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 88) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 88)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0088

/-! Kernel-checked entropy margins for general spectral rectangle 89. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0089
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5049744632, 4863585449, 4686365509, 4517549382, 4356640335, 4203176956, 4056730129, 3916900331, 3783315204, 3655627360, 3533512403, 3416667140, 3304807954, 3197669326, 3095002491, 2996574209, 2902165641, 2811571323, 2724598221, 2641064870, 2560800571, 2483644665, 2409445851, 2338061568, 2269357415, 2203206619, 2139489542, 2078093223, 2018910952, 1961841881, 1906790652, 1853667060, 1802385737, 1752865855, 1705030850, 1658808171, 1614129034, 1570928203, 1529143781, 1488717013, 1449592105, 1411716055, 1375038489, 1339511516, 1305089582, 1271729346, 1239389551, 1208030909, 1177615996, 1148109145, 1119476354, 1091685194, 1064704726, 1038505418, 1013059076, 988338767, 964318757, 940974446, 918282313, 896219855, 874765538, 853898749, 833599745, 813849614, 794630231, 775924219, 757714912, 739986322, 722723103, 705910522, 689534429, 673581230, 658037859, 642891754, 628130833, 613743473, 599718487, 586045106, 572712956, 559712047, 547032749, 534665780, 522602188, 510833338, 499350900, 488146832, 477213369, 466543014, 456128521, 445962890, 436039354, 426351371, 416892611, 407656952, 398638470, 389831429, 381230276, 372829634, 364624292, 356609203, 348779475, 341130363, 333657269, 326355732, 319221424, 312250146, 305437823, 298780498, 292274329, 285915586, 279700645, 273625986, 267688186, 261883921, 256209957, 250663153, 245240452, 239938881, 234755548, 229687639, 224732418]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 89).prefactor = (2675127343723799/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 89).cutoff/(generalMeanRows 89).c)).2 =
    (15979744453413/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 89).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 89).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 89).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 89

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 89).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 89).criticalRate j.val*(generalMeanRows 89).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 89).c*(generalMeanRows 89).criticalPoint j.val)).2-
      (generalMeanRows 89).J/2-(generalMeanRows 89).error (generalMeanGrid j.val)+
      (generalMeanRows 89).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 89).c)).2-
      (generalMeanRows 89).J/2-(generalMeanRows 89).error 4 := by
  have he : (generalMeanRows 89).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 89) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 89)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0089

/-! Kernel-checked entropy margins for general spectral rectangle 90. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0090
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5287594011, 5095541261, 4912675036, 4738444764, 4572339700, 4413885440, 4262640818, 4118195123, 3980165590, 3848195153, 3721950403, 3601119746, 3485411730, 3374553525, 3268289537, 3166380141, 3068600530, 2974739655, 2884599253, 2797992957, 2714745479, 2634691852, 2557676734, 2483553771, 2412184999, 2343440297, 2277196877, 2213338819, 2151756628, 2092346829, 2035011596, 1979658394, 1926199660, 1874552495, 1824638382, 1776382923, 1729715592, 1684569506, 1640881210, 1598590477, 1557640118, 1517975810, 1479545929, 1442301397, 1406195538, 1371183941, 1337224336, 1304276474, 1272302015, 1241264421, 1211128863, 1181862122, 1153432509, 1125809775, 1098965041, 1072870724, 1047500465, 1022829070, 998832446, 975487545, 952772312, 930665631, 909147281, 888197889, 867798885, 847932469, 828581564, 809729789, 791361418, 773461354, 756015092, 739008699, 722428780, 706262454, 690497333, 675121497, 660123469, 645492201, 631217051, 617287762, 603694451, 590427587, 577477978, 564836754, 552495356, 540445520, 528679264, 517188879, 505966915, 495006168, 484299676, 473840703, 463622733, 453639460, 443884779, 434352779, 425037735, 415934100, 407036499, 398339721, 389838715, 381528582, 373404568, 365462063, 357696591, 350103807, 342679495, 335419556, 328320012, 321376996, 314586751, 307945625, 301450068, 295096627, 288881945, 282802756, 276855881, 271038230, 265346793, 259778640, 254330920]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 90).prefactor = (5501043047918813/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 90).cutoff/(generalMeanRows 90).c)).2 =
    (407968238326299/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 90).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 90).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 90).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 90

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 90).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 90).criticalRate j.val*(generalMeanRows 90).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 90).c*(generalMeanRows 90).criticalPoint j.val)).2-
      (generalMeanRows 90).J/2-(generalMeanRows 90).error (generalMeanGrid j.val)+
      (generalMeanRows 90).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 90).c)).2-
      (generalMeanRows 90).J/2-(generalMeanRows 90).error 4 := by
  have he : (generalMeanRows 90).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 90) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 90)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0090

/-! Kernel-checked entropy margins for general spectral rectangle 91. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0091
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5293297865, 5121038231, 4956903954, 4800395177, 4651048989, 4508436177, 4372158331, 4241845244, 4117152567, 3997759706, 3883367915, 3773698569, 3668491599, 3567504068, 3470508874, 3377293568, 3287659271, 3201419683, 3118400180, 3038436977, 2961376365, 2887074008, 2815394292, 2746209727, 2679400399, 2614853455, 2552462635, 2492127834, 2433754698, 2377254247, 2322542533, 2269540310, 2218172739, 2168369107, 2120062568, 2073189900, 2027691285, 1983510092, 1940592689, 1898888254, 1858348610, 1818928065, 1780583260, 1743273037, 1706958303, 1671601911, 1637168548, 1603624629, 1570938193, 1539078814, 1508017515, 1477726682, 1448179988, 1419352324, 1391219730, 1363759329, 1336949271, 1310768676, 1285197581, 1260216891, 1235808332, 1211954408, 1188638359, 1165844126, 1143556308, 1121760134, 1100441429, 1079586580, 1059182513, 1039216663, 1019676948, 1000551749, 981829880, 963500576, 945553465, 927978553, 910766205, 893907128, 877392356, 861213234, 845361403, 829828787, 814607583, 799690242, 785069466, 770738191, 756689579, 742917009, 729414065, 716174530, 703192377, 690461761, 677977011, 665732623, 653723254, 641943717, 630388969, 619054113, 607934388, 597025164, 586321938, 575820329, 565516073, 555405021, 545483130, 535746466, 526191193, 516813574, 507609969, 498576825, 489710680, 481008158, 472465963, 464080880, 455849772, 447769575, 439837300, 432050024, 424404897, 416899130, 409530002]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 91).prefactor = (5073433996162651/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 91).cutoff/(generalMeanRows 91).c)).2 =
    (243170304633239/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 91).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 91).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 91).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 91

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 91).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 91).criticalRate j.val*(generalMeanRows 91).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 91).c*(generalMeanRows 91).criticalPoint j.val)).2-
      (generalMeanRows 91).J/2-(generalMeanRows 91).error (generalMeanGrid j.val)+
      (generalMeanRows 91).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 91).c)).2-
      (generalMeanRows 91).J/2-(generalMeanRows 91).error 4 := by
  have he : (generalMeanRows 91).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 91) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 91)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0091

/-! Kernel-checked entropy margins for general spectral rectangle 92. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0092
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7254901306, 6986450240, 6729846172, 6484447074, 6249655321, 6024913704, 5809701888, 5603533271, 5405952183, 5216531371, 5034869752, 4860590385, 4693338643, 4532780557, 4378601319, 4230503915, 4088207884, 3951448184, 3819974151, 3693548553, 3571946711, 3454955701, 3342373611, 3234008855, 3129679549, 3029212920, 2932444766, 2839218956, 2749386961, 2662807416, 2579345723, 2498873666, 2421269063, 2346415435, 2274201696, 2204521871, 2137274819, 2072363982, 2009697149, 1949186228, 1890747040, 1834299122, 1779765534, 1727072693, 1676150201, 1626930690, 1579349677, 1533345425, 1488858809, 1445833192, 1404214312, 1363950164, 1324990901, 1287288728, 1250797814, 1215474197, 1181275702, 1148161859, 1116093825, 1085034315, 1054947528, 1025799088, 997555972, 970186459, 943660069, 917947513, 893020634, 868852369, 845416692, 822688578, 800643956, 779259669, 758513437, 738383822, 718850189, 699892674, 681492155, 663630218, 646289131, 629451812, 613101807, 597223262, 581800902, 566820003, 552266373, 538126331, 524386685, 511034714, 498058149, 485445158, 473184322, 461264626, 449675440, 438406504, 427447917, 416790117, 406423875, 396340276, 386530714, 376986872, 367700719, 358664493, 349870697, 341312083, 332981646, 324872617, 316978448, 309292810, 301809583, 294522847, 287426876, 280516132, 273785254, 267229056, 260842522, 254620792, 248559166, 242653092, 236898162, 231290109, 225824799]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 92).prefactor = (384630601764083/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 92).cutoff/(generalMeanRows 92).c)).2 =
    (118939624983989/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 92).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 92).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 92).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 92

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 92).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 92).criticalRate j.val*(generalMeanRows 92).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 92).c*(generalMeanRows 92).criticalPoint j.val)).2-
      (generalMeanRows 92).J/2-(generalMeanRows 92).error (generalMeanGrid j.val)+
      (generalMeanRows 92).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 92).c)).2-
      (generalMeanRows 92).J/2-(generalMeanRows 92).error 4 := by
  have he : (generalMeanRows 92).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 92) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 92)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0092

/-! Kernel-checked entropy margins for general spectral rectangle 93. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0093
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7281963032, 7062413889, 6852507758, 6651702994, 6459495720, 6275416503, 6099027394, 5929919286, 5767709558, 5612039947, 5462574650, 5318998594, 5181015881, 5048348374, 4920734412, 4797927641, 4679695941, 4565820449, 4456094665, 4350323627, 4248323152, 4149919143, 4054946940, 3963250731, 3874682996, 3789104004, 3706381333, 3626389435, 3549009230, 3474127720, 3401637638, 3331437120, 3263429392, 3197522486, 3133628969, 3071665691, 3011553546, 2953217258, 2896585164, 2841589028, 2788163851, 2736247703, 2685781558, 2636709145, 2588976803, 2542533346, 2497329934, 2453319957, 2410458919, 2368704330, 2328015607, 2288353979, 2249682396, 2211965443, 2175169260, 2139261467, 2104211091, 2069988497, 2036565324, 2003914424, 1972009802, 1940826564, 1910340862, 1880529848, 1851371622, 1822845191, 1794930426, 1767608023, 1740859461, 1714666970, 1689013493, 1663882658, 1639258741, 1615126642, 1591471851, 1568280428, 1545538972, 1523234600, 1501354921, 1479888019, 1458822426, 1438147106, 1417851437, 1397925189, 1378358511, 1359141910, 1340266241, 1321722687, 1303502750, 1285598231, 1268001222, 1250704094, 1233699483, 1216980278, 1200539613, 1184370856, 1168467599, 1152823649, 1137433018, 1122289916, 1107388742, 1092724079, 1078290680, 1064083470, 1050097532, 1036328105, 1022770573, 1009420467, 996273450, 983325319, 970571997, 958009529, 945634074, 933441907, 921429408, 909593061, 897929453, 886435263, 875107265, 863942322, 852937384]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 93).prefactor = (52317800455761/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 93).cutoff/(generalMeanRows 93).c)).2 =
    (212738931931387/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 93).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 93).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 93).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 93

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 93).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 93).criticalRate j.val*(generalMeanRows 93).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 93).c*(generalMeanRows 93).criticalPoint j.val)).2-
      (generalMeanRows 93).J/2-(generalMeanRows 93).error (generalMeanGrid j.val)+
      (generalMeanRows 93).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 93).c)).2-
      (generalMeanRows 93).J/2-(generalMeanRows 93).error 4 := by
  have he : (generalMeanRows 93).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 93) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 93)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0093

/-! Kernel-checked entropy margins for general spectral rectangle 94. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0094
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7463728851, 7234406752, 7015161796, 6805428820, 6604682061, 6412431687, 6228220708, 6051622224, 5882236956, 5719691039, 5563634028, 5413737103, 5269691443, 5131206750, 4998009908, 4869843766, 4746466016, 4627648178, 4513174662, 4402841910, 4296457605, 4193839949, 4094816984, 3999225978, 3906912846, 3817731625, 3731543975, 3648218725, 3567631445, 3489664050, 3414204433, 3341146119, 3270387943, 3201833751, 3135392118, 3070976088, 3008502922, 2947893876, 2889073975, 2831971816, 2776519376, 2722651833, 2670307394, 2619427141, 2569954879, 2521836993, 2475022322, 2429462028, 2385109477, 2341920135, 2299851454, 2258862781, 2218915255, 2179971727, 2141996669, 2104956100, 2068817508, 2033549777, 1999123124, 1965509032, 1932680191, 1900610440, 1869274711, 1838648981, 1808710218, 1779436341, 1750806171, 1722799389, 1695396500, 1668578790, 1642328297, 1616627769, 1591460638, 1566810984, 1542663512, 1519003518, 1495816864, 1473089955, 1450809714, 1428963557, 1407539375, 1386525509, 1365910734, 1345684238, 1325835605, 1306354796, 1287232138, 1268458300, 1250024288, 1231921422, 1214141328, 1196675925, 1179517409, 1162658245, 1146091156, 1129809107, 1113805304, 1098073175, 1082606367, 1067398736, 1052444335, 1037737411, 1023272394, 1009043891, 995046678, 981275694, 967726035, 954392948, 941271823, 928358190, 915647712, 903136181, 890819511, 878693737, 866755008, 854999581, 843423821, 832024195, 820797268, 809739698, 798848238]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 94).prefactor = (5466326003801253/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 94).cutoff/(generalMeanRows 94).c)).2 =
    (414428027676191/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 94).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 94).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 94).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 94

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 94).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 94).criticalRate j.val*(generalMeanRows 94).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 94).c*(generalMeanRows 94).criticalPoint j.val)).2-
      (generalMeanRows 94).J/2-(generalMeanRows 94).error (generalMeanGrid j.val)+
      (generalMeanRows 94).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 94).c)).2-
      (generalMeanRows 94).J/2-(generalMeanRows 94).error 4 := by
  have he : (generalMeanRows 94).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 94) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 94)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0094

/-! Kernel-checked entropy margins for general spectral rectangle 95. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0095
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6497837637, 6263370022, 6039448903, 5825488116, 5620942210, 5425302854, 5238095642, 5058877243, 4887232853, 4722773910, 4565136032, 4413977162, 4268975891, 4129829929, 3996254728, 3867982214, 3744759640, 3626348532, 3512523726, 3403072481, 3297793665, 3196497006, 3099002401, 3005139275, 2914745995, 2827669316, 2743763879, 2662891738, 2584921921, 2509730025, 2437197831, 2367212958, 2299668524, 2234462846, 2171499141, 2110685265, 2051933455, 1995160093, 1940285485, 1887233649, 1835932120, 1786311768, 1738306622, 1691853706, 1646892889, 1603366735, 1561220373, 1520401362, 1480859573, 1442547073, 1405418018, 1369428549, 1334536696, 1300702288, 1267886863, 1236053588, 1205167183, 1175193844, 1146101176, 1117858126, 1090434921, 1063803008, 1037934998, 1012804611, 988386628, 964656842, 941592010, 919169812, 897368810, 876168406, 855548805, 835490985, 815976653, 796988224, 778508781, 760522052, 743012379, 725964693, 709364489, 693197799, 677451176, 662111662, 647166778, 632604496, 618413224, 604581787, 591099410, 577955700, 565140636, 552644544, 540458093, 528572273, 516978390, 505668046, 494633131, 483865811, 473358519, 463103939, 453095002, 443324875, 433786949, 424474834, 415382347, 406503508, 397832530, 389363811, 381091930, 373011637, 365117847, 357405638, 349870238, 342507026, 335311523, 328279388, 321406412, 314688513, 308121736, 301702240, 295426302, 289290309, 283290754]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 95).prefactor = (5711386893090123/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 95).cutoff/(generalMeanRows 95).c)).2 =
    (310167017351783/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 95).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 95).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 95).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 95

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 95).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 95).criticalRate j.val*(generalMeanRows 95).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 95).c*(generalMeanRows 95).criticalPoint j.val)).2-
      (generalMeanRows 95).J/2-(generalMeanRows 95).error (generalMeanGrid j.val)+
      (generalMeanRows 95).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 95).c)).2-
      (generalMeanRows 95).J/2-(generalMeanRows 95).error 4 := by
  have he : (generalMeanRows 95).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 95) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 95)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0095

/-! Kernel-checked entropy margins for general spectral rectangle 96. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0096
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6097921453, 5916080933, 5742450531, 5576550423, 5417934873, 5266189257, 5120927419, 4981789293, 4848438775, 4720561810, 4597864662, 4480072350, 4366927230, 4258187709, 4153627068, 4053032394, 3956203599, 3862952526, 3773102124, 3686485695, 3602946197, 3522335601, 3444514305, 3369350582, 3296720079, 3226505347, 3158595404, 3092885337, 3029275928, 2967673298, 2907988593, 2850137675, 2794040846, 2739622579, 2686811280, 2635539053, 2585741488, 2537357462, 2490328949, 2444600846, 2400120806, 2356839086, 2314708399, 2273683782, 2233722463, 2194783747, 2156828895, 2119821026, 2083725013, 2048507388, 2014136255, 1980581206, 1947813245, 1915804707, 1884529198, 1853961518, 1824077610, 1794854492, 1766270207, 1738303769, 1710935112, 1684145048, 1657915217, 1632228050, 1607066726, 1582415137, 1558257853, 1534580086, 1511367660, 1488606984, 1466285016, 1444389245, 1422907660, 1401828727, 1381141368, 1360834936, 1340899197, 1321324313, 1302100816, 1283219599, 1264671893, 1246449255, 1228543553, 1210946949, 1193651888, 1176651083, 1159937507, 1143504378, 1127345148, 1111453494, 1095823308, 1080448686, 1065323921, 1050443496, 1035802070, 1021394476, 1007215711, 993260932, 979525444, 966004698, 952694285, 939589927, 926687477, 913982907, 901472309, 889151887, 877017952, 865066923, 853295315, 841699741, 830276908, 819023608, 807936723, 797013215, 786250125, 775644571, 765193746, 754894910, 744745397, 734742601, 724883984]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 96).prefactor = (237004792140441/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 96).cutoff/(generalMeanRows 96).c)).2 =
    (469280486521167/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 96).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 96).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 96).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 96

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 96).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 96).criticalRate j.val*(generalMeanRows 96).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 96).c*(generalMeanRows 96).criticalPoint j.val)).2-
      (generalMeanRows 96).J/2-(generalMeanRows 96).error (generalMeanGrid j.val)+
      (generalMeanRows 96).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 96).c)).2-
      (generalMeanRows 96).J/2-(generalMeanRows 96).error 4 := by
  have he : (generalMeanRows 96).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 96) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 96)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0096

/-! Kernel-checked entropy margins for general spectral rectangle 97. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0097
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6183638471, 5995673587, 5816201900, 5644727956, 5480791485, 5323964329, 5173847707, 5030069764, 4892283379, 4760164179, 4633408764, 4511733086, 4394870991, 4282572885, 4174604524, 4070745912, 3970790285, 3874543194, 3781821648, 3692453340, 3606275925, 3523136365, 3442890312, 3365401549, 3290541466, 3218188579, 3148228079, 3080551421, 3015055933, 2951644462, 2890225035, 2830710550, 2773018485, 2717070630, 2662792828, 2610114746, 2558969648, 2509294190, 2461028231, 2414114642, 2368499148, 2324130156, 2280958617, 2238937878, 2198023552, 2158173396, 2119347192, 2081506639, 2044615249, 2008638250, 1973542495, 1939296377, 1905869746, 1873233832, 1841361176, 1810225560, 1779801941, 1750066395, 1720996056, 1692569064, 1664764511, 1637562399, 1610943587, 1584889754, 1559383353, 1534407578, 1509946323, 1485984150, 1462506256, 1439498442, 1416947082, 1394839098, 1373161933, 1351903526, 1331052285, 1310597073, 1290527177, 1270832295, 1251502514, 1232528293, 1213900444, 1195610119, 1177648790, 1160008239, 1142680541, 1125658053, 1108933400, 1092499461, 1076349364, 1060476467, 1044874357, 1029536829, 1014457889, 999631736, 985052757, 970715521, 956614765, 942745397, 929102478, 915681224, 902476994, 889485290, 876701743, 864122118, 851742300, 839558293, 827566215, 815762295, 804142864, 792704357, 781443305, 770356334, 759440158, 748691579, 738107483, 727684835, 717420680, 707312136, 697356392, 687550710, 677892417]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 97).prefactor = (980010141136097/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 97).cutoff/(generalMeanRows 97).c)).2 =
    (229689707769229/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 97).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 97).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 97).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 97

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 97).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 97).criticalRate j.val*(generalMeanRows 97).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 97).c*(generalMeanRows 97).criticalPoint j.val)).2-
      (generalMeanRows 97).J/2-(generalMeanRows 97).error (generalMeanGrid j.val)+
      (generalMeanRows 97).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 97).c)).2-
      (generalMeanRows 97).J/2-(generalMeanRows 97).error 4 := by
  have he : (generalMeanRows 97).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 97) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 97)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0097

/-! Kernel-checked entropy margins for general spectral rectangle 98. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0098
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6153631387, 5959562162, 5774285361, 5597289806, 5428100584, 5266275877, 5111404142, 4963101587, 4821009907, 4684794242, 4554141343, 4428757901, 4308369048, 4192716978, 4081559704, 3974669919, 3871833953, 3772850822, 3677531353, 3585697380, 3497181004, 3411823917, 3329476768, 3249998583, 3173256232, 3099123927, 3027482764, 2958220294, 2891230124, 2826411549, 2763669210, 2702912767, 2644056608, 2587019563, 2531724648, 2478098823, 2426072758, 2375580628, 2326559908, 2278951190, 2232698005, 2187746661, 2144046088, 2101547695, 2060205231, 2019974662, 1980814046, 1942683424, 1905544712, 1869361604, 1834099470, 1799725279, 1766207505, 1733516054, 1701622190, 1670498459, 1640118631, 1610457632, 1581491488, 1553197266, 1525553026, 1498537766, 1472131382, 1446314615, 1421069018, 1396376908, 1372221334, 1348586039, 1325455429, 1302814537, 1280648994, 1258945004, 1237689313, 1216869184, 1196472374, 1176487108, 1156902063, 1137706339, 1118889447, 1100441285, 1082352123, 1064612587, 1047213638, 1030146563, 1013402957, 996974709, 980853993, 965033249, 949505177, 934262725, 919299075, 904607636, 890182034, 876016100, 862103866, 848439554, 835017567, 821832485, 808879054, 796152181, 783646928, 771358506, 759282268, 747413701, 735748428, 724282196, 713010872, 701930441, 691037002, 680326760, 669796024, 659441204, 649258807, 639245432, 629397766, 619712587, 610186752, 600817200, 591600947, 582535085, 573616778]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 98).prefactor = (158293851765321/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 98).cutoff/(generalMeanRows 98).c)).2 =
    (109966650328719/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 98).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 98).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 98).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 98

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 98).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 98).criticalRate j.val*(generalMeanRows 98).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 98).c*(generalMeanRows 98).criticalPoint j.val)).2-
      (generalMeanRows 98).J/2-(generalMeanRows 98).error (generalMeanGrid j.val)+
      (generalMeanRows 98).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 98).c)).2-
      (generalMeanRows 98).J/2-(generalMeanRows 98).error 4 := by
  have he : (generalMeanRows 98).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 98) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 98)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0098

/-! Kernel-checked entropy margins for general spectral rectangle 99. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0099
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5591921152, 5394115000, 5205436766, 5025360015, 4853395494, 4689087886, 4532012918, 4381774766, 4238003741, 4100354188, 3968502613, 3842145967, 3721000110, 3604798400, 3493290417, 3386240798, 3283428172, 3184644181, 3089692587, 2998388450, 2910557371, 2826034795, 2744665371, 2666302352, 2590807052, 2518048333, 2447902138, 2380251046, 2314983874, 2251995291, 2191185474, 2132459773, 2075728409, 2020906190, 1967912242, 1916669762, 1867105783, 1819150962, 1772739366, 1727808294, 1684298085, 1642151960, 1601315859, 1561738295, 1523370213, 1486164862, 1450077671, 1415066131, 1381089691, 1348109650, 1316089065, 1284992657, 1254786728, 1225439076, 1196918922, 1169196837, 1142244676, 1116035509, 1090543564, 1065744169, 1041613698, 1018129518, 995269942, 973014185, 951342316, 930235220, 909674559, 889642734, 870122852, 851098690, 832554666, 814475808, 796847728, 779656591, 762889093, 746532437, 730574309, 715002855, 699806663, 684974742, 670496504, 656361746, 642560631, 629083677, 615921739, 603065991, 590507919, 578239303, 566252208, 554538968, 543092179, 531904684, 520969567, 510280141, 499829938, 489612702, 479622379, 469853109, 460299220, 450955220, 441815787, 432875766, 424130164, 415574137, 407202991, 399012174, 390997270, 383153994, 375478189, 367965818, 360612965, 353415823, 346370698, 339474000, 332722239, 326112025, 319640063, 313303148, 307098164, 301022079, 295071946]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 99).prefactor = (523633564059191/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 99).cutoff/(generalMeanRows 99).c)).2 =
    (374422693062493/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 99).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 99).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 99).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 99

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 99).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 99).criticalRate j.val*(generalMeanRows 99).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 99).c*(generalMeanRows 99).criticalPoint j.val)).2-
      (generalMeanRows 99).J/2-(generalMeanRows 99).error (generalMeanGrid j.val)+
      (generalMeanRows 99).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 99).c)).2-
      (generalMeanRows 99).J/2-(generalMeanRows 99).error 4 := by
  have he : (generalMeanRows 99).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 99) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 99)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0099

/-! Kernel-checked entropy margins for general spectral rectangle 100. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0100
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5757767131, 5577451869, 5405386830, 5241083344, 5084087829, 4933978728, 4790363778, 4652877563, 4521179317, 4394950945, 4273895236, 4157734243, 4046207822, 3939072289, 3836099212, 3737074301, 3641796391, 3550076514, 3461737053, 3376610949, 3294540993, 3215379153, 3138985967, 3065229978, 2993987211, 2925140689, 2858579985, 2794200809, 2731904617, 2671598260, 2613193643, 2556607421, 2501760706, 2448578801, 2396990946, 2346930083, 2298332642, 2251138332, 2205289948, 2160733197, 2117416529, 2075290977, 2034310012, 1994429406, 1955607102, 1917803089, 1880979295, 1845099475, 1810129111, 1776035319, 1742786759, 1710353552, 1678707200, 1647820515, 1617667545, 1588223514, 1559464753, 1531368650, 1503913586, 1477078893, 1450844796, 1425192373, 1400103510, 1375560857, 1351547795, 1328048393, 1305047380, 1282530105, 1260482512, 1238891110, 1217742942, 1197025562, 1176727009, 1156835784, 1137340830, 1118231505, 1099497570, 1081129164, 1063116789, 1045451294, 1028123857, 1011125970, 994449427, 978086306, 962028962, 946270010, 930802315, 915618981, 900713341, 886078947, 871709558, 857599136, 843741832, 830131984, 816764102, 803632868, 790733123, 778059866, 765608241, 753373539, 741351184, 729536735, 717925875, 706514412, 695298266, 684273473, 673436177, 662782625, 652309164, 642012239, 631888387, 621934234, 612146495, 602521966, 593057524, 583750124, 574596796, 565594642, 556740835, 548032614, 539467286]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 100).prefactor = (98014434520351/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 100).cutoff/(generalMeanRows 100).c)).2 =
    (230840456263367/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 100).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 100).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 100).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 100

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 100).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 100).criticalRate j.val*(generalMeanRows 100).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 100).c*(generalMeanRows 100).criticalPoint j.val)).2-
      (generalMeanRows 100).J/2-(generalMeanRows 100).error (generalMeanGrid j.val)+
      (generalMeanRows 100).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 100).c)).2-
      (generalMeanRows 100).J/2-(generalMeanRows 100).error 4 := by
  have he : (generalMeanRows 100).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 100) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 100)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0100

/-! Kernel-checked entropy margins for general spectral rectangle 101. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0101
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5306312027, 5122559524, 4947348238, 4780176281, 4620577644, 4468119066, 4322397243, 4183036325, 4049685667, 3922017810, 3799726652, 3682525795, 3570147046, 3462339054, 3358866070, 3259506812, 3164053432, 3072310567, 2984094469, 2899232207, 2817560930, 2738927194, 2663186335, 2590201892, 2519845076, 2451994277, 2386534602, 2323357460, 2262360158, 2203445545, 2146521665, 2091501444, 2038302394, 1986846339, 1937059157, 1888870543, 1842213784, 1797025550, 1753245700, 1710817097, 1669685438, 1629799094, 1591108959, 1553568310, 1517132674, 1481759701, 1447409055, 1414042296, 1381622783, 1350115574, 1319487336, 1289706261, 1260741982, 1232565500, 1205149111, 1178466338, 1152491871, 1127201503, 1102572075, 1078581423, 1055208328, 1032432468, 1010234374, 988595386, 967497613, 946923899, 926857781, 907283461, 888185772, 869550144, 851362583, 833609637, 816278374, 799356355, 782831616, 766692640, 750928340, 735528039, 720481451, 705778662, 691410118, 677366603, 663639227, 650219413, 637098880, 624269633, 611723951, 599454372, 587453685, 575714918, 564231330, 552996399, 542003813, 531247464, 520721438, 510420006, 500337619, 490468900, 480808636, 471351774, 462093411, 453028794, 444153308, 435462475, 426951949, 418617507, 410455049, 402460591, 394630262, 386960299, 379447043, 372086937, 364876521, 357812427, 350891382, 344110195, 337465765, 330955070, 324575166, 318323188, 312196344]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 101).prefactor = (2524007575905689/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 101).cutoff/(generalMeanRows 101).c)).2 =
    (407856262512957/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 101).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 101).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 101).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 101

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 101).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 101).criticalRate j.val*(generalMeanRows 101).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 101).c*(generalMeanRows 101).criticalPoint j.val)).2-
      (generalMeanRows 101).J/2-(generalMeanRows 101).error (generalMeanGrid j.val)+
      (generalMeanRows 101).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 101).c)).2-
      (generalMeanRows 101).J/2-(generalMeanRows 101).error 4 := by
  have he : (generalMeanRows 101).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 101) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 101)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0101

/-! Kernel-checked entropy margins for general spectral rectangle 102. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0102
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4826904745, 4642055023, 4466031761, 4298318053, 4138433752, 3985932275, 3840397740, 3701442406, 3568704373, 3441845513, 3320549600, 3204520619, 3093481235, 2987171392, 2885347051, 2787779028, 2694251934, 2604563207, 2518522221, 2435949472, 2356675823, 2280541813, 2207397019, 2137099465, 2069515080, 2004517187, 1941986042, 1881808396, 1823877094, 1768090701, 1714353152, 1662573429, 1612665259, 1564546832, 1518140541, 1473372732, 1430173477, 1388476363, 1348218285, 1309339263, 1271782266, 1235493045, 1200419981, 1166513936, 1133728124, 1102017975, 1071341022, 1041656783, 1012926660, 985113834, 958183174, 932101148, 906835740, 882356371, 858633826, 835640183, 813348747, 791733990, 770771490, 750437879, 730710785, 711568789, 692991375, 674958884, 657452479, 640454098, 623946421, 607912832, 592337391, 577204794, 562500350, 548209949, 534320037, 520817589, 507690084, 494925485, 482512216, 470439139, 458695536, 447271092, 436155875, 425340319, 414815212, 404571674, 394601149, 384895386, 375446431, 366246611, 357288523, 348565022, 340069213, 331794439, 323734268, 315882491, 308233107, 300780317, 293518515, 286442282, 279546378, 272825732, 266275441, 259890759, 253667093, 247599996, 241685164, 235918426, 230295745, 224813207, 219467021, 214253513, 209169121, 204210391, 199373974, 194656623, 190055186, 185566609, 181187923, 176916251, 172748799, 168682854, 164715783]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 102).prefactor = (1039947109734179/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 102).cutoff/(generalMeanRows 102).c)).2 =
    (174258411363323/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 102).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 102).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 102).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 102

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 102).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 102).criticalRate j.val*(generalMeanRows 102).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 102).c*(generalMeanRows 102).criticalPoint j.val)).2-
      (generalMeanRows 102).J/2-(generalMeanRows 102).error (generalMeanGrid j.val)+
      (generalMeanRows 102).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 102).c)).2-
      (generalMeanRows 102).J/2-(generalMeanRows 102).error 4 := by
  have he : (generalMeanRows 102).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 102) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 102)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0102

/-! Kernel-checked entropy margins for general spectral rectangle 103. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0103
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5384369294, 5214478051, 5052438064, 4897775555, 4750051271, 4608857464, 4473815193, 4344571907, 4220799272, 4102191212, 3988462136, 3879345341, 3774591556, 3673967617, 3577255269, 3484250060, 3394760340, 3308606341, 3225619333, 3145640847, 3068521969, 2994122676, 2922311237, 2852963654, 2785963146, 2721199673, 2658569493, 2597974757, 2539323124, 2482527418, 2427505290, 2374178926, 2322474755, 2272323190, 2223658383, 2176417999, 2130542995, 2085977431, 2042668279, 2000565249, 1959620631, 1919789140, 1881027775, 1843295688, 1806554058, 1770765976, 1735896334, 1701911725, 1668780346, 1636471908, 1604957552, 1574209769, 1544202325, 1514910196, 1486309494, 1458377411, 1431092162, 1404432923, 1378379788, 1352913716, 1328016486, 1303670655, 1279859515, 1256567060, 1233777945, 1211477454, 1189651468, 1168286436, 1147369345, 1126887695, 1106829469, 1087183117, 1067937526, 1049082003, 1030606252, 1012500358, 994754767, 977360269, 960307983, 943589339, 927196069, 911120187, 895353980, 879889995, 864721028, 849840111, 835240502, 820915677, 806859321, 793065315, 779527731, 766240825, 753199025, 740396928, 727829290, 715491024, 703377188, 691482984, 679803749, 668334950, 657072184, 646011165, 635147726, 624477811, 613997473, 603702869, 593590255, 583655986, 573896508, 564308358, 554888160, 545632622, 536538532, 527602758, 518822242, 510193999, 501715116, 493382748, 485194117, 477146507, 469237267]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 103).prefactor = (4826666109475081/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 103).cutoff/(generalMeanRows 103).c)).2 =
    (477606929297723/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 103).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 103).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 103).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 103

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 103).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 103).criticalRate j.val*(generalMeanRows 103).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 103).c*(generalMeanRows 103).criticalPoint j.val)).2-
      (generalMeanRows 103).J/2-(generalMeanRows 103).error (generalMeanGrid j.val)+
      (generalMeanRows 103).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 103).c)).2-
      (generalMeanRows 103).J/2-(generalMeanRows 103).error 4 := by
  have he : (generalMeanRows 103).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 103) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 103)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0103

/-! Kernel-checked entropy margins for general spectral rectangle 104. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0104
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5325466959, 5151539047, 4985690455, 4827435182, 4676322579, 4531934263, 4393881353, 4261801993, 4135359129, 4014238500, 3898146829, 3786810182, 3679972477, 3577394134, 3478850842, 3384132430, 3293041843, 3205394199, 3121015924, 3039743961, 2961425040, 2885915010, 2813078214, 2742786924, 2674920809, 2609366454, 2546016899, 2484771229, 2425534183, 2368215791, 2312731046, 2258999587, 2206945414, 2156496617, 2107585123, 2060146468, 2014119575, 1969446549, 1926072493, 1883945323, 1843015609, 1803236416, 1764563159, 1726953469, 1690367063, 1654765630, 1620112711, 1586373603, 1553515254, 1521506177, 1490316357, 1459917174, 1430281325, 1401382753, 1373196580, 1345699042, 1318867431, 1292680038, 1267116099, 1242155749, 1217779971, 1193970555, 1170710054, 1147981747, 1125769601, 1104058236, 1082832892, 1062079398, 1041784146, 1021934057, 1002516561, 983519569, 964931449, 946741009, 928937470, 911510449, 894449944, 877746308, 861390241, 845372769, 829685231, 814319265, 799266793, 784520010, 770071373, 755913584, 742039588, 728442555, 715115874, 702053143, 689248161, 676694917, 664387587, 652320520, 640488238, 628885424, 617506916, 606347703, 595402920, 584667837, 574137860, 563808523, 553675483, 543734515, 533981511, 524412470, 515023501, 505810812, 496770714, 487899609, 479193996, 470650459, 462265669, 454036383, 445959436, 438031739, 430250282, 422612127, 415114403, 407754312, 400529119]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 104).prefactor = (4955627105637763/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 104).cutoff/(generalMeanRows 104).c)).2 =
    (230182561431609/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 104).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 104).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 104).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 104

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 104).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 104).criticalRate j.val*(generalMeanRows 104).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 104).c*(generalMeanRows 104).criticalPoint j.val)).2-
      (generalMeanRows 104).J/2-(generalMeanRows 104).error (generalMeanGrid j.val)+
      (generalMeanRows 104).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 104).c)).2-
      (generalMeanRows 104).J/2-(generalMeanRows 104).error 4 := by
  have he : (generalMeanRows 104).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 104) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 104)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0104

/-! Kernel-checked entropy margins for general spectral rectangle 105. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0105
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5570584508, 5391725723, 5221152903, 5058366859, 4902904745, 4754336887, 4612263934, 4476314322, 4346141978, 4221424263, 4101860106, 3987168321, 3877086072, 3771367485, 3669782381, 3572115114, 3478163519, 3387737942, 3300660351, 3216763521, 3135890286, 3057892847, 2982632138, 2909977236, 2839804819, 2771998668, 2706449199, 2643053033, 2581712600, 2522335766, 2464835490, 2409129503, 2355140014, 2302793429, 2252020099, 2202754070, 2154932871, 2108497294, 2063391205, 2019561361, 1976957236, 1935530865, 1895236694, 1856031441, 1817873961, 1780725130, 1744547725, 1709306319, 1674967181, 1641498175, 1608868682, 1577049504, 1546012796, 1515731987, 1486181711, 1457337744, 1429176940, 1401677177, 1374817298, 1348577065, 1322937107, 1297878878, 1273384610, 1249437279, 1226020561, 1203118799, 1180716971, 1158800654, 1137355998, 1116369697, 1095828958, 1075721483, 1056035439, 1036759439, 1017882518, 999394115, 981284054, 963542525, 946160067, 929127551, 912436169, 896077413, 880043067, 864325191, 848916110, 833808401, 818994884, 804468609, 790222849, 776251087, 762547012, 749104505, 735917635, 722980649, 710287966, 697834171, 685614004, 673622360, 661854279, 650304940, 638969658, 627843879, 616923172, 606203226, 595679848, 585348954, 575206569, 565248822, 555471941, 545872251, 536446169, 527190206, 518100954, 509175094, 500409385, 491800666, 483345852, 475041931, 466885962, 458875075, 451006463]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 105).prefactor = (2544016869317123/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 105).cutoff/(generalMeanRows 105).c)).2 =
    (29309304159663/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 105).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 105).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 105).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 105

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 105).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 105).criticalRate j.val*(generalMeanRows 105).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 105).c*(generalMeanRows 105).criticalPoint j.val)).2-
      (generalMeanRows 105).J/2-(generalMeanRows 105).error (generalMeanGrid j.val)+
      (generalMeanRows 105).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 105).c)).2-
      (generalMeanRows 105).J/2-(generalMeanRows 105).error 4 := by
  have he : (generalMeanRows 105).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 105) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 105)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0105

/-! Kernel-checked entropy margins for general spectral rectangle 106. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0106
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5379722612, 5204284346, 5037059542, 4877548597, 4725288532, 4579849786, 4440833349, 4307868190, 4180608948, 4058733842, 3941942796, 3829955727, 3722511006, 3619364043, 3520286010, 3425062673, 3333493320, 3245389784, 3160575546, 3078884913, 3000162259, 2924261327, 2851044593, 2780382666, 2712153747, 2646243120, 2582542687, 2520950532, 2461370522, 2403711933, 2347889105, 2293821118, 2241431501, 2190647944, 2141402048, 2093629079, 2047267743, 2002259984, 1958550777, 1916087957, 1874822041, 1834706072, 1795695470, 1757747890, 1720823098, 1684882842, 1649890742, 1615812183, 1582614213, 1550265450, 1518735993, 1487997340, 1458022311, 1428784975, 1400260579, 1372425487, 1345257117, 1318733888, 1292835161, 1267541192, 1242833088, 1218692754, 1195102859, 1172046792, 1149508629, 1127473093, 1105925523, 1084851845, 1064238541, 1044072619, 1024341592, 1005033449, 986136633, 967640019, 949532895, 931804940, 914446207, 897447103, 880798377, 864491099, 848516651, 832866706, 817533221, 802508423, 787784793, 773355059, 759212185, 745349360, 731759986, 718437675, 705376233, 692569658, 680012127, 667697994, 655621778, 643778161, 632161975, 620768204, 609591974, 598628544, 587873310, 577321791, 566969629, 556812585, 546846532, 537067451, 527471429, 518054657, 508813421, 499744102, 490843174, 482107197, 473532819, 465116768, 456855853, 448746961, 440787051, 432973158, 425302384, 417771901, 410378945]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 106).prefactor = (203241157813783/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 106).cutoff/(generalMeanRows 106).c)).2 =
    (118317131924781/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 106).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 106).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 106).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 106

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 106).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 106).criticalRate j.val*(generalMeanRows 106).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 106).c*(generalMeanRows 106).criticalPoint j.val)).2-
      (generalMeanRows 106).J/2-(generalMeanRows 106).error (generalMeanGrid j.val)+
      (generalMeanRows 106).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 106).c)).2-
      (generalMeanRows 106).J/2-(generalMeanRows 106).error 4 := by
  have he : (generalMeanRows 106).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 106) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 106)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0106

/-! Kernel-checked entropy margins for general spectral rectangle 107. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0107
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5347815043, 5170443337, 5001399925, 4840178952, 4686311615, 4539362918, 4398928770, 4264633385, 4136126946, 4013083493, 3895199021, 3782189757, 3673790594, 3569753665, 3469847053, 3373853606, 3281569855, 3192805024, 3107380126, 3025127128, 2945888187, 2869514943, 2795867871, 2724815684, 2656234776, 2590008716, 2526027768, 2464188461, 2404393177, 2346549775, 2290571244, 2236375378, 2183884470, 2133025036, 2083727549, 2035926200, 1989558666, 1944565903, 1900891944, 1858483718, 1817290875, 1777265626, 1738362595, 1700538673, 1663752890, 1627966291, 1593141820, 1559244211, 1526239887, 1494096867, 1462784674, 1432274250, 1402537884, 1373549130, 1345282743, 1317714611, 1290821697, 1264581979, 1238974396, 1213978796, 1189575893, 1165747215, 1142475067, 1119742489, 1097533217, 1075831649, 1054622813, 1033892332, 1013626397, 993811737, 974435594, 955485697, 936950238, 918817854, 901077597, 883718923, 866731669, 850106035, 833832569, 817902149, 802305970, 787035527, 772082606, 757439265, 743097828, 729050870, 715291205, 701811881, 688606164, 675667532, 662989667, 650566444, 638391925, 626460350, 614766131, 603303844, 592068226, 581054163, 570256688, 559670977, 549292337, 539116209, 529138159, 519353871, 509759148, 500349906, 491122166, 482072056, 473195805, 464489737, 455950273, 447573922, 439357283, 431297038, 423389953, 415632873, 408022718, 400556484, 393231241, 386044124, 378992342]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 107).prefactor = (2573213011006617/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 107).cutoff/(generalMeanRows 107).c)).2 =
    (464757838031217/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 107).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 107).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 107).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 107

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 107).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 107).criticalRate j.val*(generalMeanRows 107).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 107).c*(generalMeanRows 107).criticalPoint j.val)).2-
      (generalMeanRows 107).J/2-(generalMeanRows 107).error (generalMeanGrid j.val)+
      (generalMeanRows 107).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 107).c)).2-
      (generalMeanRows 107).J/2-(generalMeanRows 107).error 4 := by
  have he : (generalMeanRows 107).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 107) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 107)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0107

/-! Kernel-checked entropy margins for general spectral rectangle 108. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0108
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4965228713, 4786967847, 4617158617, 4455295847, 4300910921, 4153568592, 4012864122, 3878420727, 3749887277, 3626936225, 3509261735, 3396577988, 3288617644, 3185130446, 3085881947, 2990652348, 2899235434, 2811437608, 2727076994, 2645982620, 2567993668, 2492958780, 2420735415, 2351189270, 2284193723, 2219629340, 2157383403, 2097349481, 2039427026, 1983521006, 1929541556, 1877403659, 1827026843, 1778334911, 1731255672, 1685720709, 1641665144, 1599027437, 1557749182, 1517774927, 1479052002, 1441530358, 1405162416, 1369902928, 1335708842, 1302539182, 1270354929, 1239118916, 1208795720, 1179351573, 1150754267, 1122973071, 1095978655, 1069743007, 1044239371, 1019442178, 995326981, 971870402, 949050070, 926844576, 905233419, 884196961, 863716384, 843773650, 824351461, 805433219, 787002999, 769045511, 751546067, 734490561, 717865430, 701657638, 685854643, 670444380, 655415237, 640756032, 626455995, 612504750, 598892297, 585608992, 572645537, 559992958, 547642597, 535586094, 523815377, 512322647, 501100367, 490141254, 479438265, 468984588, 458773633, 448799022, 439054582, 429534335, 420232492, 411143443, 402261754, 393582155, 385099539, 376808952, 368705589, 360784787, 353042022, 345472901, 338073161, 330838659, 323765374, 316849397, 310086930, 303474282, 297007864, 290684188, 284499860, 278451580, 272536136, 266750405, 261091345, 255555998, 250141482, 244844991, 239663793]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 108).prefactor = (5155557843012159/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 108).cutoff/(generalMeanRows 108).c)).2 =
    (82070940457711/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 108).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 108).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 108).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 108

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 108).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 108).criticalRate j.val*(generalMeanRows 108).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 108).c*(generalMeanRows 108).criticalPoint j.val)).2-
      (generalMeanRows 108).J/2-(generalMeanRows 108).error (generalMeanGrid j.val)+
      (generalMeanRows 108).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 108).c)).2-
      (generalMeanRows 108).J/2-(generalMeanRows 108).error 4 := by
  have he : (generalMeanRows 108).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 108) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 108)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0108

/-! Kernel-checked entropy margins for general spectral rectangle 109. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0109
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4941887088, 4761854164, 4590390868, 4426985280, 4271162496, 4122481398, 3980531759, 3844931658, 3715325151, 3591380174, 3472786650, 3359254769, 3250513440, 3146308870, 3046403280, 2950573726, 2858611025, 2770318774, 2685512444, 2604018554, 2525673910, 2450324900, 2377826852, 2308043435, 2240846110, 2176113617, 2113731505, 2053591698, 1995592082, 1939636136, 1885632578, 1833495043, 1783141776, 1734495355, 1687482426, 1642033458, 1598082518, 1555567054, 1514427697, 1474608076, 1436054645, 1398716516, 1362545313, 1327495023, 1293521867, 1260584172, 1228642254, 1197658310, 1167596313, 1138421912, 1110102346, 1082606355, 1055904100, 1029967088, 1004768100, 980281124, 956481291, 933344819, 910848952, 888971910, 867692841, 846991769, 826849557, 807247856, 788169075, 769596337, 751513448, 733904861, 716755646, 700051462, 683778526, 667923586, 652473901, 637417212, 622741722, 608436075, 594489334, 580890964, 567630812, 554699093, 542086370, 529783541, 517781823, 506072739, 494648105, 483500017, 472620840, 462003195, 451639950, 441524208, 431649299, 422008770, 412596378, 403406077, 394432016, 385668527, 377110120, 368751474, 360587433, 352612999, 344823325, 337213710, 329779593, 322516550, 315420286, 308486631, 301711539, 295091077, 288621428, 282298882, 276119833, 270080780, 264178315, 258409128, 252769998, 247257796, 241869473, 236602068, 231452695, 226418548, 221496896]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 109).prefactor = (5223978070510759/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 109).cutoff/(generalMeanRows 109).c)).2 =
    (80451498411187/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 109).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 109).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 109).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 109

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 109).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 109).criticalRate j.val*(generalMeanRows 109).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 109).c*(generalMeanRows 109).criticalPoint j.val)).2-
      (generalMeanRows 109).J/2-(generalMeanRows 109).error (generalMeanGrid j.val)+
      (generalMeanRows 109).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 109).c)).2-
      (generalMeanRows 109).J/2-(generalMeanRows 109).error 4 := by
  have he : (generalMeanRows 109).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 109) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 109)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0109

/-! Kernel-checked entropy margins for general spectral rectangle 110. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0110
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4919178722, 4737393054, 4564295988, 4399368740, 4242130011, 4092132708, 3948961022, 3812227806, 3681572220, 3556657606, 3437169573, 3322814259, 3213316755, 3108419678, 3007881860, 2911477166, 2818993397, 2730231301, 2645003659, 2563134441, 2484458044, 2408818572, 2336069192, 2266071521, 2198695074, 2133816746, 2071320333, 2011096093, 1953040330, 1897055021, 1843047452, 1790929896, 1740619306, 1692037026, 1645108528, 1599763164, 1555933935, 1513557275, 1472572847, 1432923358, 1394554383, 1357414195, 1321453617, 1286625874, 1252886458, 1220193002, 1188505158, 1157784491, 1127994367, 1099099861, 1071067661, 1043865980, 1017464479, 991834185, 966947421, 942777738, 919299853, 896489582, 874323792, 852780341, 831838029, 811476552, 791676456, 772419093, 753686585, 735461782, 717728229, 700470132, 683672323, 667320236, 651399873, 635897778, 620801016, 606097142, 591774183, 577820616, 564225345, 550977684, 538067337, 525484381, 513219253, 501262726, 489605902, 478240196, 467157319, 456349271, 445808322, 435527008, 425498113, 415714664, 406169920, 396857359, 387770672, 378903757, 370250705, 361805796, 353563492, 345518428, 337665407, 329999391, 322515498, 315208996, 308075293, 301109940, 294308615, 287667130, 281181416, 274847525, 268661624, 262619990, 256719008, 250955166, 245325049, 239825343, 234452822, 229204354, 224076891, 219067471, 214173212, 209391311, 204719040]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 110).prefactor = (2646653156861203/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 110).cutoff/(generalMeanRows 110).c)).2 =
    (24639082522417/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 110).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 110).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 110).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 110

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 110).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 110).criticalRate j.val*(generalMeanRows 110).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 110).c*(generalMeanRows 110).criticalPoint j.val)).2-
      (generalMeanRows 110).J/2-(generalMeanRows 110).error (generalMeanGrid j.val)+
      (generalMeanRows 110).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 110).c)).2-
      (generalMeanRows 110).J/2-(generalMeanRows 110).error 4 := by
  have he : (generalMeanRows 110).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 110) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 110)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0110

/-! Kernel-checked entropy margins for general spectral rectangle 111. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0111
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7512015270, 7291650072, 7080718773, 6878701587, 6685114770, 6499507430, 6321458677, 6150575101, 5986488512, 5828853906, 5677347654, 5531665852, 5391522838, 5256649853, 5126793809, 5001716187, 4881192014, 4765008943, 4652966397, 4544874791, 4440554819, 4339836788, 4242560016, 4148572263, 4057729217, 3969894007, 3884936763, 3802734192, 3723169202, 3646130536, 3571512440, 3499214350, 3429140603, 3361200163, 3295306363, 3231376673, 3169332472, 3109098840, 3050604358, 2993780929, 2938563600, 2884890400, 2832702184, 2781942494, 2732557416, 2684495456, 2637707415, 2592146278, 2547767103, 2504526921, 2462384639, 2421300946, 2381238231, 2342160499, 2304033291, 2266823617, 2230499879, 2195031813, 2160390419, 2126547907, 2093477639, 2061154075, 2029552723, 1998650092, 1968423645, 1938851754, 1909913663, 1881589445, 1853859965, 1826706849, 1800112442, 1774059784, 1748532575, 1723515145, 1698992431, 1674949946, 1651373755, 1628250453, 1605567139, 1583311396, 1561471272, 1540035255, 1518992260, 1498331607, 1478043005, 1458116537, 1438542640, 1419312097, 1400416016, 1381845820, 1363593234, 1345650269, 1328009215, 1310662628, 1293603318, 1276824338, 1260318977, 1244080748, 1228103381, 1212380812, 1196907177, 1181676802, 1166684197, 1151924049, 1137391214, 1123080709, 1108987710, 1095107541, 1081435673, 1067967713, 1054699405, 1041626618, 1028745347, 1016051705, 1003541920, 991212331, 979059381, 967079616, 955269682, 943626317, 932146352]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 111).prefactor = (5096863777079071/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 111).cutoff/(generalMeanRows 111).c)).2 =
    (102833339119153/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 111).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 111).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 111).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 111

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 111).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 111).criticalRate j.val*(generalMeanRows 111).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 111).c*(generalMeanRows 111).criticalPoint j.val)).2-
      (generalMeanRows 111).J/2-(generalMeanRows 111).error (generalMeanGrid j.val)+
      (generalMeanRows 111).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 111).c)).2-
      (generalMeanRows 111).J/2-(generalMeanRows 111).error 4 := by
  have he : (generalMeanRows 111).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 111) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 111)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0111

/-! Kernel-checked entropy margins for general spectral rectangle 112. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0112
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7730691757, 7499597500, 7278398424, 7066550149, 6863546039, 6668913855, 6482212781, 6303030769, 6130982178, 5965705647, 5806862190, 5654133474, 5507220265, 5365841022, 5229730613, 5098639153, 4972330941, 4850583488, 4733186631, 4619941710, 4510660823, 4405166134, 4303289233, 4204870551, 4109758816, 4017810544, 3928889577, 3842866643, 3759618961, 3679029853, 3600988407, 3525389140, 3452131699, 3381120573, 3312264827, 3245477855, 3180677142, 3117784048, 3056723600, 2997424298, 2939817938, 2883839436, 2829426667, 2776520319, 2725063745, 2675002829, 2626285863, 2578863423, 2532688257, 2487715179, 2443900968, 2401204270, 2359585513, 2319006815, 2279431907, 2240826057, 2203155992, 2166389838, 2130497044, 2095448331, 2061215622, 2027771997, 1995091632, 1963149753, 1931922585, 1901387311, 1871522024, 1842305690, 1813718105, 1785739861, 1758352311, 1731537531, 1705278293, 1679558033, 1654360819, 1629671328, 1605474816, 1581757096, 1558504510, 1535703910, 1513342636, 1491408491, 1469889728, 1448775023, 1428053466, 1407714536, 1387748090, 1368144342, 1348893855, 1329987520, 1311416548, 1293172451, 1275247035, 1257632386, 1240320859, 1223305064, 1206577861, 1190132346, 1173961845, 1158059901, 1142420268, 1127036900, 1111903948, 1097015748, 1082366815, 1067951836, 1053765665, 1039803312, 1026059943, 1012530871, 999211548, 986097566, 973184646, 960468634, 947945501, 935611331, 923462324, 911494788, 899705133, 888089873, 876645617]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 112).prefactor = (2672577347027949/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 112).cutoff/(generalMeanRows 112).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 112).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 112).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 112).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 112

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 112).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 112).criticalRate j.val*(generalMeanRows 112).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 112).c*(generalMeanRows 112).criticalPoint j.val)).2-
      (generalMeanRows 112).J/2-(generalMeanRows 112).error (generalMeanGrid j.val)+
      (generalMeanRows 112).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 112).c)).2-
      (generalMeanRows 112).J/2-(generalMeanRows 112).error 4 := by
  have he : (generalMeanRows 112).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 112) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 112)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0112

/-! Kernel-checked entropy margins for general spectral rectangle 113. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0113
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7015412726, 6776214665, 6547414053, 6328443632, 6118775377, 5917917007, 5725408892, 5540821293, 5363751897, 5193823616, 5030682595, 4873996428, 4723452540, 4578756726, 4439631815, 4305816468, 4177064068, 4053141714, 3933829298, 3818918657, 3708212792, 3601525157, 3498678991, 3399506715, 3303849361, 3211556054, 3122483526, 3036495665, 2953463099, 2873262806, 2795777750, 2720896545, 2648513138, 2578526514, 2510840423, 2445363115, 2382007106, 2320688947, 2261329009, 2203851289, 2148183215, 2094255476, 2042001850, 1991359050, 1942266578, 1894666582, 1848503729, 1803725075, 1760279956, 1718119871, 1677198379, 1637471004, 1598895134, 1561429941, 1525036291, 1489676665, 1455315088, 1421917054, 1389449458, 1357880534, 1327179793, 1297317965, 1268266944, 1239999736, 1212490409, 1185714045, 1159646699, 1134265351, 1109547868, 1085472966, 1062020172, 1039169790, 1016902867, 995201159, 974047105, 953423796, 933314946, 913704869, 894578452, 875921128, 857718862, 839958119, 822625850, 805709470, 789196840, 773076247, 757336388, 741966353, 726955612, 712293994, 697971679, 683979179, 670307330, 656947274, 643890451, 631128586, 618653677, 606457986, 594534028, 582874563, 571472583, 560321307, 549414171, 538744819, 528307097, 518095045, 508102886, 498325028, 488756046, 479390687, 470223854, 461250608, 452466158, 443865856, 435445194, 427199798, 419125421, 411217943, 403473362, 395887793, 388457464]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 113).prefactor = (5605540966559077/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 113).cutoff/(generalMeanRows 113).c)).2 =
    (315002247538181/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 113).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 113).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 113).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 113

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 113).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 113).criticalRate j.val*(generalMeanRows 113).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 113).c*(generalMeanRows 113).criticalPoint j.val)).2-
      (generalMeanRows 113).J/2-(generalMeanRows 113).error (generalMeanGrid j.val)+
      (generalMeanRows 113).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 113).c)).2-
      (generalMeanRows 113).J/2-(generalMeanRows 113).error 4 := by
  have he : (generalMeanRows 113).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 113) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 113)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0113

/-! Kernel-checked entropy margins for general spectral rectangle 114. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0114
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6212438400, 6027470774, 5850676037, 5681587066, 5519769577, 5364819254, 5216359192, 5074037608, 4937525793, 4806516270, 4680721131, 4559870536, 4443711356, 4332005933, 4224530957, 4121076442, 4021444787, 3925449920, 3832916508, 3743679239, 3657582153, 3574478028, 3494227820, 3416700134, 3341770746, 3269322151, 3199243148, 3131428458, 3065778360, 3002198361, 2940598885, 2880894981, 2823006057, 2766855624, 2712371060, 2659483394, 2608127095, 2558239881, 2509762537, 2462638747, 2416814932, 2372240102, 2328865717, 2286645550, 2245535570, 2205493819, 2166480304, 2128456895, 2091387225, 2055236601, 2019971915, 1985561561, 1951975363, 1919184496, 1887161422, 1855879823, 1825314538, 1795441509, 1766237723, 1737681161, 1709750749, 1682426311, 1655688527, 1629518889, 1603899662, 1578813848, 1554245150, 1530177938, 1506597217, 1483488597, 1460838266, 1438632961, 1416859944, 1395506973, 1374562287, 1354014575, 1333852963, 1314066988, 1294646583, 1275582058, 1256864081, 1238483666, 1220432153, 1202701198, 1185282755, 1168169064, 1151352641, 1134826262, 1118582955, 1102615987, 1086918854, 1071485273, 1056309169, 1041384670, 1026706098, 1012267956, 998064928, 984091865, 970343783, 956815852, 943503392, 930401868, 917506883, 904814169, 892319590, 880019128, 867908884, 855985072, 844244013, 832682135, 821295962, 810082117, 799037317, 788158365, 777442152, 766885651, 756485915, 746240074, 736145333, 726198967, 716398319]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 114).prefactor = (4672355818508523/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 114).cutoff/(generalMeanRows 114).c)).2 =
    (443962678536877/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 114).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 114).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 114).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 114

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 114).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 114).criticalRate j.val*(generalMeanRows 114).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 114).c*(generalMeanRows 114).criticalPoint j.val)).2-
      (generalMeanRows 114).J/2-(generalMeanRows 114).error (generalMeanGrid j.val)+
      (generalMeanRows 114).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 114).c)).2-
      (generalMeanRows 114).J/2-(generalMeanRows 114).error 4 := by
  have he : (generalMeanRows 114).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 114) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 114)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0114

/-! Kernel-checked entropy margins for general spectral rectangle 115. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0115
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6317755157, 6126125495, 5942970710, 5767807254, 5600185561, 5439687071, 5285921585, 5138524898, 4997156676, 4861498554, 4731252412, 4606138824, 4485895648, 4370276753, 4259050850, 4152000432, 4048920807, 3949619209, 3853913983, 3761633838, 3672617161, 3586711380, 3503772378, 3423663957, 3346257335, 3271430683, 3199068694, 3129062187, 3061307733, 2995707313, 2932167994, 2870601632, 2810924590, 2753057479, 2696924914, 2642455286, 2589580547, 2538236013, 2488360174, 2439894523, 2392783384, 2346973764, 2302415204, 2259059645, 2216861296, 2175776518, 2135763707, 2096783186, 2058797108, 2021769357, 1985665462, 1950452510, 1916099066, 1882575099, 1849851910, 1817902066, 1786699336, 1756218629, 1726435941, 1697328297, 1668873706, 1641051105, 1613840323, 1587222029, 1561177698, 1535689567, 1510740603, 1486314465, 1462395473, 1438968577, 1416019324, 1393533835, 1371498776, 1349901329, 1328729176, 1307970470, 1287613814, 1267648243, 1248063204, 1228848534, 1209994447, 1191491513, 1173330648, 1155503090, 1138000395, 1120814413, 1103937284, 1087361418, 1071079490, 1055084423, 1039369381, 1023927756, 1008753162, 993839423, 979180563, 964770801, 950604543, 936676369, 922981031, 909513448, 896268690, 883241982, 870428692, 857824328, 845424530, 833225067, 821221832, 809410834, 797788200, 786350162, 775093060, 764013335, 753107527, 742372268, 731804281, 721400377, 711157451, 701072478, 691142513, 681364685, 671736196]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 115).prefactor = (193664209757339/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 115).cutoff/(generalMeanRows 115).c)).2 =
    (86812321510833/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 115).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 115).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 115).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 115

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 115).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 115).criticalRate j.val*(generalMeanRows 115).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 115).c*(generalMeanRows 115).criticalPoint j.val)).2-
      (generalMeanRows 115).J/2-(generalMeanRows 115).error (generalMeanGrid j.val)+
      (generalMeanRows 115).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 115).c)).2-
      (generalMeanRows 115).J/2-(generalMeanRows 115).error 4 := by
  have he : (generalMeanRows 115).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 115) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 115)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0115

/-! Kernel-checked entropy margins for general spectral rectangle 116. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0116
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6425742640, 6227282632, 6037610727, 5856226320, 5682663972, 5516490326, 5357301374, 5204720002, 5058393799, 4917993082, 4783209116, 4653752508, 4529351752, 4409751902, 4294713371, 4184010832, 4077432217, 3974777794, 3875859332, 3780499321, 3688530262, 3599794013, 3514141182, 3431430569, 3351528646, 3274309081, 3199652294, 3127445039, 3057580027, 2989955564, 2924475224, 2861047532, 2799585683, 2740007267, 2682234018, 2626191580, 2571809283, 2519019941, 2467759653, 2417967626, 2369586002, 2322559700, 2276836263, 2232365722, 2189100455, 2146995070, 2106006284, 2066092811, 2027215261, 1989336039, 1952419254, 1916430628, 1881337421, 1847108344, 1813713492, 1781124272, 1749313336, 1718254524, 1687922799, 1658294194, 1629345762, 1601055523, 1573402419, 1546366266, 1519927717, 1494068217, 1468769970, 1444015899, 1419789613, 1396075375, 1372858073, 1350123189, 1327856771, 1306045407, 1284676203, 1263736757, 1243215134, 1223099850, 1203379849, 1184044484, 1165083498, 1146487009, 1128245489, 1110349755, 1092790946, 1075560517, 1058650220, 1042052091, 1025758441, 1009761843, 994055119, 978631333, 963483778, 948605967, 933991624, 919634676, 905529244, 891669636, 878050338, 864666006, 851511464, 838581690, 825871817, 813377122, 801093023, 789015073, 777138953, 765460470, 753975550, 742680234, 731570674, 720643130, 709893963, 699319635, 688916702, 678681812, 668611702, 658703195, 648953195, 639358688, 629916735]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 116).prefactor = (5016985488396911/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 116).cutoff/(generalMeanRows 116).c)).2 =
    (212128803728773/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 116).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 116).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 116).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 116

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 116).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 116).criticalRate j.val*(generalMeanRows 116).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 116).c*(generalMeanRows 116).criticalPoint j.val)).2-
      (generalMeanRows 116).J/2-(generalMeanRows 116).error (generalMeanGrid j.val)+
      (generalMeanRows 116).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 116).c)).2-
      (generalMeanRows 116).J/2-(generalMeanRows 116).error 4 := by
  have he : (generalMeanRows 116).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 116) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 116)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0116

/-! Kernel-checked entropy margins for general spectral rectangle 117. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0117
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5971410656, 5767807456, 5573346449, 5387510657, 5209819291, 5039824580, 4877108957, 4721282529, 4571980823, 4428862754, 4291608793, 4159919314, 4033513094, 3912125954, 3795509520, 3683430095, 3575667627, 3472014765, 3372275992, 3276266834, 3183813123, 3094750330, 3008922936, 2926183862, 2846393939, 2769421410, 2695141480, 2623435889, 2554192517, 2487305023, 2422672495, 2360199143, 2299793994, 2241370616, 2184846865, 2130144635, 2077189640, 2025911193, 1976242014, 1928118040, 1881478254, 1836264514, 1792421405, 1749896093, 1708638185, 1668599605, 1629734468, 1591998972, 1555351289, 1519751460, 1485161305, 1451544330, 1418865641, 1387091869, 1356191088, 1326132748, 1296887604, 1268427654, 1240726080, 1213757186, 1187496349, 1161919963, 1137005394, 1112730932, 1089075750, 1066019857, 1043544066, 1021629950, 1000259812, 979416648, 959084118, 939246514, 919888731, 900996241, 882555067, 864551758, 846973365, 829807421, 813041917, 796665285, 780666376, 765034442, 749759124, 734830426, 720238709, 705974670, 692029329, 678394017, 665060362, 652020275, 639265943, 626789813, 614584584, 602643195, 590958817, 579524844, 568334882, 557382742, 546662432, 536168149, 525894273, 515835356, 505986121, 496341451, 486896385, 477646110, 468585961, 459711407, 451018054, 442501636, 434158010, 425983152, 417973156, 410124225, 402432669, 394894903, 387507439, 380266889, 373169954, 366213428, 359394191]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 117).prefactor = (5198718632074221/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 117).cutoff/(generalMeanRows 117).c)).2 =
    (183685116527747/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 117).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 117).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 117).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 117

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 117).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 117).criticalRate j.val*(generalMeanRows 117).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 117).c*(generalMeanRows 117).criticalPoint j.val)).2-
      (generalMeanRows 117).J/2-(generalMeanRows 117).error (generalMeanGrid j.val)+
      (generalMeanRows 117).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 117).c)).2-
      (generalMeanRows 117).J/2-(generalMeanRows 117).error 4 := by
  have he : (generalMeanRows 117).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 117) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 117)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0117

/-! Kernel-checked entropy margins for general spectral rectangle 118. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0118
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5910241478, 5725207862, 5548479757, 5379576004, 5218049571, 5063484570, 4915493605, 4773715396, 4637812643, 4507470112, 4382392900, 4262304869, 4146947229, 4036077243, 3929467057, 3826902624, 3728182727, 3633118079, 3541530503, 3453252174, 3368124923, 3285999596, 3206735465, 3130199678, 3056266758, 2984818130, 2915741691, 2848931405, 2784286932, 2721713278, 2661120470, 2602423258, 2545540834, 2490396564, 2436917752, 2385035403, 2334684018, 2285801383, 2238328393, 2192208869, 2147389397, 2103819171, 2061449852, 2020235431, 1980132099, 1941098131, 1903093770, 1866081124, 1830024063, 1794888130, 1760640447, 1727249635, 1694685737, 1662920139, 1631925507, 1601675716, 1572145788, 1543311840, 1515151018, 1487641456, 1460762217, 1434493254, 1408815361, 1383710133, 1359159927, 1335147825, 1311657597, 1288673669, 1266181090, 1244165507, 1222613127, 1201510702, 1180845492, 1160605252, 1140778198, 1121352995, 1102318731, 1083664898, 1065381377, 1047458413, 1029886609, 1012656900, 995760544, 979189106, 962934445, 946988698, 931344274, 915993837, 900930297, 886146798, 871636710, 857393620, 843411321, 829683802, 816205244, 802970009, 789972635, 777207825, 764670446, 752355516, 740258203, 728373818, 716697807, 705225749, 693953348, 682876433, 671990944, 661292940, 650778585, 640444147, 630285995, 620300597, 610484513, 600834391, 591346969, 582019068, 572847589, 563829511, 554961889, 546241852, 537666598]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 118).prefactor = (2436595304069419/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 118).cutoff/(generalMeanRows 118).c)).2 =
    (218181552271223/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 118).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 118).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 118).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 118

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 118).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 118).criticalRate j.val*(generalMeanRows 118).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 118).c*(generalMeanRows 118).criticalPoint j.val)).2-
      (generalMeanRows 118).J/2-(generalMeanRows 118).error (generalMeanGrid j.val)+
      (generalMeanRows 118).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 118).c)).2-
      (generalMeanRows 118).J/2-(generalMeanRows 118).error 4 := by
  have he : (generalMeanRows 118).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 118) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 118)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0118

/-! Kernel-checked entropy margins for general spectral rectangle 119. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0119
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5376550384, 5188216485, 5008502537, 4836913145, 4672987880, 4516298224, 4366444853, 4223055197, 4085781263, 3954297665, 3828299852, 3707502505, 3591638085, 3480455509, 3373718952, 3271206747, 3172710381, 3078033582, 2986991476, 2899409809, 2815124241, 2733979689, 2655829721, 2580536001, 2507967766, 2438001355, 2370519760, 2305412219, 2242573829, 2181905194, 2123312095, 2066705176, 2011999666, 1959115102, 1907975083, 1858507039, 1810642006, 1764314424, 1719461950, 1676025271, 1633947941, 1593176220, 1553658929, 1515347310, 1478194891, 1442157372, 1407192501, 1373259970, 1340321311, 1308339801, 1277280372, 1247109521, 1217795234, 1189306911, 1161615288, 1134692376, 1108511393, 1083046706, 1058273773, 1034169088, 1010710134, 987875329, 965643986, 943996266, 922913139, 902376347, 882368364, 862872362, 843872181, 825352295, 807297784, 789694307, 772528071, 755785811, 739454764, 723522646, 707977632, 692808332, 678003778, 663553398, 649447005, 635674775, 622227236, 609095249, 596269996, 583742966, 571505942, 559550987, 547870436, 536456880, 525303161, 514402355, 503747769, 493332927, 483151565, 473197620, 463465220, 453948684, 444642506, 435541354, 426640059, 417933614, 409417162, 401085995, 392935546, 384961384, 377159210, 369524852, 362054257, 354743493, 347588740, 340586286, 333732525, 327023954, 320457167, 314028852, 307735789, 301574848, 295542982, 289637227, 283854699]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 119).prefactor = (5029788580087083/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 119).cutoff/(generalMeanRows 119).c)).2 =
    (74768549512223/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 119).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 119).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 119).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 119

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 119).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 119).criticalRate j.val*(generalMeanRows 119).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 119).c*(generalMeanRows 119).criticalPoint j.val)).2-
      (generalMeanRows 119).J/2-(generalMeanRows 119).error (generalMeanGrid j.val)+
      (generalMeanRows 119).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 119).c)).2-
      (generalMeanRows 119).J/2-(generalMeanRows 119).error 4 := by
  have he : (generalMeanRows 119).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 119) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 119)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0119

/-! Kernel-checked entropy margins for general spectral rectangle 120. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0120
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5485764531, 5315271471, 5152510854, 4997025473, 4848390996, 4706213099, 4570124903, 4439784677, 4314873781, 4195094808, 4080169906, 3969839264, 3863859729, 3762003563, 3664057297, 3569820693, 3479105792, 3391736046, 3307545513, 3226378132, 3148087041, 3072533956, 2999588603, 2929128183, 2861036886, 2795205434, 2731530668, 2669915152, 2610266817, 2552498625, 2496528251, 2442277804, 2389673547, 2338645648, 2289127948, 2241057739, 2194375560, 2149025008, 2104952553, 2062107380, 2020441225, 1979908232, 1940464814, 1902069528, 1864682949, 1828267562, 1792787651, 1758209203, 1724499814, 1691628599, 1659566110, 1628284259, 1597756244, 1567956483, 1538860543, 1510445084, 1482687802, 1455567372, 1429063395, 1403156359, 1377827581, 1353059176, 1328834009, 1305135658, 1281948381, 1259257081, 1237047272, 1215305049, 1194017061, 1173170484, 1152752994, 1132752743, 1113158336, 1093958811, 1075143617, 1056702594, 1038625956, 1020904273, 1003528455, 986489735, 969779658, 953390059, 937313061, 921541051, 906066676, 890882830, 875982639, 861359456, 847006850, 832918594, 819088661, 805511209, 792180582, 779091293, 766238025, 753615618, 741219068, 729043516, 717084244, 705336671, 693796346, 682458943, 671320256, 660376197, 649622786, 639056153, 628672532, 618468255, 608439750, 598583539, 588896231, 579374523, 570015195, 560815107, 551771195, 542880472, 534140023, 525547002, 517098631, 508792198, 500625054]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 120).prefactor = (293025346125431/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 120).cutoff/(generalMeanRows 120).c)).2 =
    (230511400641093/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 120).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 120).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 120).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 120

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 120).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 120).criticalRate j.val*(generalMeanRows 120).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 120).c*(generalMeanRows 120).criticalPoint j.val)).2-
      (generalMeanRows 120).J/2-(generalMeanRows 120).error (generalMeanGrid j.val)+
      (generalMeanRows 120).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 120).c)).2-
      (generalMeanRows 120).J/2-(generalMeanRows 120).error 4 := by
  have he : (generalMeanRows 120).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 120) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 120)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0120

/-! Kernel-checked entropy margins for general spectral rectangle 121. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0121
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5340085109, 5165464128, 4998822031, 4839689180, 4687629625, 4542238167, 4403137730, 4269977013, 4142428376, 4020185939, 3902963863, 3790494796, 3682528466, 3578830393, 3479180730, 3383373189, 3291214073, 3202521382, 3117123995, 3034860921, 2955580604, 2879140291, 2805405441, 2734249187, 2665551831, 2599200385, 2535088136, 2473114253, 2413183415, 2355205467, 2299095102, 2244771564, 2192158371, 2141183056, 2091776930, 2043874854, 1997415031, 1952338811, 1908590507, 1866117223, 1824868697, 1784797147, 1745857133, 1708005425, 1671200877, 1635404315, 1600578425, 1566687651, 1533698101, 1501577456, 1470294882, 1439820957, 1410127587, 1381187944, 1352976394, 1325468435, 1298640641, 1272470602, 1246936876, 1222018935, 1197697122, 1173952606, 1150767338, 1128124016, 1106006044, 1084397501, 1063283104, 1042648178, 1022478627, 1002760909, 983482002, 964629387, 946191019, 928155307, 910511092, 893247627, 876354561, 859821913, 843640064, 827799736, 812291976, 797108146, 782239903, 767679191, 753418226, 739449484, 725765692, 712359815, 699225047, 686354801, 673742700, 661382570, 649268428, 637394476, 625755095, 614344837, 603158417, 592190706, 581436730, 570891656, 560550794, 550409587, 540463608, 530708554, 521140242, 511754605, 502547687, 493515639, 484654717, 475961274, 467431762, 459062724, 450850795, 442792694, 434885225, 427125273, 419509802, 412035850, 404700529, 397501022, 390434581]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 121).prefactor = (4821857200164489/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 121).cutoff/(generalMeanRows 121).c)).2 =
    (435047314878927/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 121).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 121).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 121).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 121

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 121).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 121).criticalRate j.val*(generalMeanRows 121).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 121).c*(generalMeanRows 121).criticalPoint j.val)).2-
      (generalMeanRows 121).J/2-(generalMeanRows 121).error (generalMeanGrid j.val)+
      (generalMeanRows 121).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 121).c)).2-
      (generalMeanRows 121).J/2-(generalMeanRows 121).error 4 := by
  have he : (generalMeanRows 121).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 121) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 121)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0121

/-! Kernel-checked entropy margins for general spectral rectangle 122. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0122
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5461276245, 5288716809, 5124067258, 4966855542, 4816643759, 4673025173, 4535621550, 4404080772, 4278074692, 4157297200, 4041462478, 3930303422, 3823570205, 3721028975, 3622460666, 3527659919, 3436434085, 3348602321, 3263994760, 3182451742, 3103823116, 3027967590, 2954752135, 2884051435, 2815747374, 2749728574, 2685889947, 2624132300, 2564361958, 2506490412, 2450433998, 2396113599, 2343454358, 2292385423, 2242839702, 2194753634, 2148066982, 2102722630, 2058666402, 2015846889, 1974215287, 1933725243, 1894332721, 1855995861, 1818674861, 1782331856, 1746930815, 1712437432, 1678819032, 1646044484, 1614084113, 1582909618, 1552494005, 1522811507, 1493837526, 1465548565, 1437922172, 1410936885, 1384572177, 1358808411, 1333626792, 1309009324, 1284938766, 1261398600, 1238372985, 1215846733, 1193805267, 1172234598, 1151121292, 1130452441, 1110215642, 1090398969, 1070990951, 1051980550, 1033357140, 1015110490, 997230740, 979708389, 962534276, 945699565, 929195728, 913014535, 897148036, 881588554, 866328667, 851361200, 836679213, 822275994, 808145043, 794280070, 780674980, 767323869, 754221013, 741360865, 728738043, 716347323, 704183639, 692242070, 680517838, 669006300, 657702944, 646603386, 635703360, 624998719, 614485427, 604159558, 594017287, 584054891, 574268745, 564655315, 555211159, 545932920, 536817327, 527861188, 519061391, 510414899, 501918749, 493570046, 485365967, 477303754, 469380713]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 122).prefactor = (4824746620357339/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 122).cutoff/(generalMeanRows 122).c)).2 =
    (116216975880073/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 122).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 122).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 122).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 122

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 122).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 122).criticalRate j.val*(generalMeanRows 122).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 122).c*(generalMeanRows 122).criticalPoint j.val)).2-
      (generalMeanRows 122).J/2-(generalMeanRows 122).error (generalMeanGrid j.val)+
      (generalMeanRows 122).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 122).c)).2-
      (generalMeanRows 122).J/2-(generalMeanRows 122).error 4 := by
  have he : (generalMeanRows 122).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 122) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 122)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0122

/-! Kernel-checked entropy margins for general spectral rectangle 123. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0123
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5238343031, 5064271117, 4898243501, 4739782198, 4588443714, 4443816036, 4305515941, 4173186588, 4046495344, 3925131844, 3808806218, 3697247503, 3590202190, 3487432912, 3388717244, 3293846609, 3202625278, 3114869454, 3030406435, 2949073838, 2870718895, 2795197797, 2722375092, 2652123130, 2584321549, 2518856800, 2455621707, 2394515059, 2335441231, 2278309833, 2223035385, 2169537010, 2117738153, 2067566321, 2018952831, 1971832585, 1926143858, 1881828093, 1838829721, 1797095982, 1756576763, 1717224449, 1678993772, 1641841688, 1605727241, 1570611454, 1536457213, 1503229165, 1470893624, 1439418472, 1408773084, 1378928237, 1349856042, 1321529866, 1293924272, 1267014950, 1240778661, 1215193180, 1190237242, 1165890495, 1142133451, 1118947443, 1096314581, 1074217717, 1052640406, 1031566867, 1010981957, 990871134, 971220431, 952016427, 933246219, 914897400, 896958034, 879416634, 862262140, 845483900, 829071650, 813015500, 797305909, 781933680, 766889933, 752166101, 737753908, 723645362, 709832741, 696308577, 683065653, 670096985, 657395817, 644955609, 632770028, 620832941, 609138405, 597680661, 586454124, 575453381, 564673179, 554108419, 543754156, 533605584, 523658040, 513906990, 504348031, 494976884, 485789385, 476781488, 467949257, 459288861, 450796573, 442468764, 434301901, 426292545, 418437343, 410733030, 403176425, 395764426, 388494009, 381362227, 374366203, 367503134, 360770282]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 123).prefactor = (4890802433776187/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 123).cutoff/(generalMeanRows 123).c)).2 =
    (439115407417877/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 123).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 123).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 123).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 123

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 123).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 123).criticalRate j.val*(generalMeanRows 123).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 123).c*(generalMeanRows 123).criticalPoint j.val)).2-
      (generalMeanRows 123).J/2-(generalMeanRows 123).error (generalMeanGrid j.val)+
      (generalMeanRows 123).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 123).c)).2-
      (generalMeanRows 123).J/2-(generalMeanRows 123).error 4 := by
  have he : (generalMeanRows 123).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 123) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 123)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0123

/-! Kernel-checked entropy margins for general spectral rectangle 124. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0124
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5130781347, 4954850701, 4787035127, 4626858596, 4473879140, 4327685884, 4187896393, 4054154290, 3926127130, 3803504470, 3685996136, 3573330655, 3465253825, 3361527422, 3261928025, 3166245930, 3074284175, 2985857635, 2900792195, 2818923995, 2740098726, 2664170994, 2591003721, 2520467601, 2452440593, 2386807454, 2323459302, 2262293216, 2203211865, 2146123155, 2090939911, 2037579577, 1985963933, 1936018840, 1887673991, 1840862689, 1795521631, 1751590715, 1709012853, 1667733794, 1627701969, 1588868333, 1551186227, 1514611243, 1479101098, 1444615519, 1411116130, 1378566352, 1346931302, 1316177703, 1286273799, 1257189276, 1228895178, 1201363847, 1174568843, 1148484891, 1123087815, 1098354485, 1074262759, 1050791438, 1027920216, 1005629635, 983901043, 962716557, 942059019, 921911967, 902259597, 883086733, 864378796, 846121776, 828302207, 810907136, 793924104, 777341123, 761146651, 745329573, 729879182, 714785162, 700037566, 685626804, 671543626, 657779104, 644324622, 631171863, 618312789, 605739638, 593444908, 581421343, 569661931, 558159885, 546908639, 535901838, 525133329, 514597152, 504287535, 494198882, 484325771, 474662945, 465205304, 455947903, 446885941, 438014762, 429329841, 420826788, 412501338, 404349347, 396366788, 388549746, 380894418, 373397103, 366054202, 358862215, 351817735, 344917447, 338158124, 331536624, 325049889, 318694937, 312468866, 306368849, 300392128]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 124).prefactor = (2445000408566259/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 124).cutoff/(generalMeanRows 124).c)).2 =
    (102432376723659/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 124).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 124).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 124).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 124

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 124).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 124).criticalRate j.val*(generalMeanRows 124).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 124).c*(generalMeanRows 124).criticalPoint j.val)).2-
      (generalMeanRows 124).J/2-(generalMeanRows 124).error (generalMeanGrid j.val)+
      (generalMeanRows 124).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 124).c)).2-
      (generalMeanRows 124).J/2-(generalMeanRows 124).error 4 := by
  have he : (generalMeanRows 124).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 124) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 124)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0124

/-! Kernel-checked entropy margins for general spectral rectangle 125. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0125
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4934475022, 4757598825, 4588971681, 4428110781, 4274567782, 4127925795, 3987796711, 3853818788, 3725654500, 3602988592, 3485526321, 3372991872, 3265126915, 3161689300, 3062451857, 2967201313, 2875737299, 2787871434, 2703426493, 2622235639, 2544141719, 2468996610, 2396660624, 2327001953, 2259896156, 2195225688, 2132879460, 2072752431, 2014745233, 1958763819, 1904719136, 1852526823, 1802106929, 1753383645, 1706285064, 1660742947, 1616692512, 1574072231, 1532823647, 1492891193, 1454222031, 1416765899, 1380474965, 1345303696, 1311208724, 1278148734, 1246084349, 1214978025, 1184793954, 1155497969, 1127057460, 1099441287, 1072619709, 1046564306, 1021247912, 996644552, 972729379, 949478618, 926869510, 904880264, 883490005, 862678731, 842427269, 822717236, 803530997, 784851632, 766662899, 748949204, 731695570, 714887606, 698511479, 682553892, 667002055, 651843665, 637066879, 622660298, 608612945, 594914246, 581554011, 568522420, 555810003, 543407627, 531306483, 519498067, 507974171, 496726870, 485748509, 475031693, 464569274, 454354343, 444380219, 434640440, 425128754, 415839112, 406765658, 397902723, 389244814, 380786613, 372522967, 364448879, 356559509, 348850162, 341316283, 333953456, 326757396, 319723944, 312849061, 306128829, 299559441, 293137200, 286858515, 280719895, 274717950, 268849383, 263110988, 257499650, 252012337, 246646102, 241398075, 236265467, 231245561]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 125).prefactor = (4959107455679313/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 125).cutoff/(generalMeanRows 125).c)).2 =
    (192518447152133/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 125).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 125).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 125).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 125

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 125).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 125).criticalRate j.val*(generalMeanRows 125).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 125).c*(generalMeanRows 125).criticalPoint j.val)).2-
      (generalMeanRows 125).J/2-(generalMeanRows 125).error (generalMeanGrid j.val)+
      (generalMeanRows 125).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 125).c)).2-
      (generalMeanRows 125).J/2-(generalMeanRows 125).error 4 := by
  have he : (generalMeanRows 125).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 125) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 125)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0125

/-! Kernel-checked entropy margins for general spectral rectangle 126. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0126
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5120656556, 4945006331, 4777526176, 4617731727, 4465173517, 4319433922, 4180124447, 4046883285, 3919373124, 3797279178, 3680307401, 3568182877, 3460648350, 3357462902, 3258400734, 3163250065, 3071812116, 2983900188, 2899338814, 2817962973, 2739617382, 2664155829, 2591440567, 2521341750, 2453736918, 2388510511, 2325553430, 2264762619, 2206040685, 2149295545, 2094440091, 2041391887, 1990072880, 1940409136, 1892330590, 1845770818, 1800666816, 1756958800, 1714590020, 1673506580, 1633657276, 1594993438, 1557468791, 1521039313, 1485663112, 1451300308, 1417912918, 1385464752, 1353921317, 1323249720, 1293418587, 1264397975, 1236159302, 1208675266, 1181919788, 1155867937, 1130495877, 1105780809, 1081700914, 1058235306, 1035363985, 1013067789, 991328355, 970128074, 949450060, 929278111, 909596674, 890390816, 871646192, 853349018, 835486043, 818044524, 801012204, 784377286, 768128413, 752254648, 736745454, 721590677, 706780527, 692305563, 678156676, 664325075, 650802274, 637580079, 624650571, 612006100, 599639269, 587542927, 575710155, 564134261, 552808764, 541727392, 530884070, 520272912, 509888215, 499724450, 489776258, 480038438, 470505948, 461173893, 452037523, 443092225, 434333519, 425757055, 417358604, 409134058, 401079423, 393190815, 385464456, 377896674, 370483894, 363222636, 356109515, 349141234, 342314582, 335626435, 329073745, 322653546, 316362947, 310199128, 304159343]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 126).prefactor = (4957762620176619/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 126).cutoff/(generalMeanRows 126).c)).2 =
    (52788536137687/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 126).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 126).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 126).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 126

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 126).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 126).criticalRate j.val*(generalMeanRows 126).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 126).c*(generalMeanRows 126).criticalPoint j.val)).2-
      (generalMeanRows 126).J/2-(generalMeanRows 126).error (generalMeanGrid j.val)+
      (generalMeanRows 126).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 126).c)).2-
      (generalMeanRows 126).J/2-(generalMeanRows 126).error 4 := by
  have he : (generalMeanRows 126).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 126) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 126)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0126

/-! Kernel-checked entropy margins for general spectral rectangle 127. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0127
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5190763685, 5012708625, 4842935492, 4680953291, 4526306399, 4378571477, 4237354711, 4102289338, 3973033430, 3849267891, 3730694648, 3617035022, 3508028235, 3403430071, 3303011639, 3206558258, 3113868428, 3024752894, 2939033786, 2856543826, 2777125602, 2700630901, 2626920091, 2555861548, 2487331135, 2421211711, 2357392682, 2295769581, 2236243683, 2178721643, 2123115161, 2069340671, 2017319053, 1966975361, 1918238570, 1871041346, 1825319823, 1781013398, 1738064546, 1696418631, 1656023748, 1616830562, 1578792163, 1541863927, 1506003390, 1471170123, 1437325625, 1404433210, 1372457912, 1341366389, 1311126836, 1281708902, 1253083612, 1225223291, 1198101502, 1171692974, 1145973545, 1120920101, 1096510527, 1072723651, 1049539198, 1026937744, 1004900674, 983410139, 962449022, 942000898, 922050001, 902581195, 883579938, 865032256, 846924718, 829244407, 811978897, 795116229, 778644892, 762553799, 746832268, 731470006, 716457090, 701783948, 687441348, 673420378, 659712436, 646309215, 633202689, 620385101, 607848956, 595587002, 583592228, 571857847, 560377293, 549144205, 538152427, 527395991, 516869117, 506566199, 496481806, 486610665, 476947665, 467487845, 458226388, 449158619, 440279998, 431586113, 423072679, 414735530, 406570618, 398574007, 390741867, 383070474, 375556205, 368195533, 360985025, 353921341, 347001226, 340221511, 333579108, 327071010, 320694286, 314446078, 308323601]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 127).prefactor = (5025639561368001/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 127).cutoff/(generalMeanRows 127).c)).2 =
    (52788536137687/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 127).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 127).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 127).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 127

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 127).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 127).criticalRate j.val*(generalMeanRows 127).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 127).c*(generalMeanRows 127).criticalPoint j.val)).2-
      (generalMeanRows 127).J/2-(generalMeanRows 127).error (generalMeanGrid j.val)+
      (generalMeanRows 127).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 127).c)).2-
      (generalMeanRows 127).J/2-(generalMeanRows 127).error 4 := by
  have he : (generalMeanRows 127).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 127) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 127)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0127

/-! Kernel-checked entropy margins for general spectral rectangle 128. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0128
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5281364298, 5112238450, 4950854357, 4796750770, 4649499829, 4508704145, 4373994195, 4245025983, 4121478944, 4003054054, 3889472116, 3780472220, 3675810338, 3575258046, 3478601365, 3385639702, 3296184875, 3210060233, 3127099837, 3047147715, 2970057173, 2895690167, 2823916713, 2754614352, 2687667654, 2622967755, 2560411933, 2499903212, 2441349995, 2384665726, 2329768572, 2276581132, 2225030160, 2175046313, 2126563913, 2079520724, 2033857751, 1989519038, 1946451500, 1904604742, 1863930913, 1824384551, 1785922448, 1748503522, 1712088693, 1676640775, 1642124363, 1608505738, 1575752771, 1543834839, 1512722738, 1482388605, 1452805851, 1423949087, 1395794062, 1368317600, 1341497548, 1315312717, 1289742833, 1264768491, 1240371109, 1216532885, 1193236757, 1170466369, 1148206031, 1126440685, 1105155879, 1084337732, 1063972908, 1044048590, 1024552452, 1005472638, 986797738, 968516768, 950619150, 933094690, 915933564, 899126300, 882663759, 866537123, 850737879, 835257807, 820088963, 805223673, 790654514, 776374310, 762376116, 748653211, 735199087, 722007442, 709072169, 696387350, 683947246, 671746293, 659779092, 648040403, 636525140, 625228364, 614145278, 603271219, 592601658, 582132189, 571858528, 561776509, 551882077, 542171287, 532640296, 523285365, 514102848, 505089197, 496240952, 487554742, 479027279, 470655359, 462435854, 454365714, 446441964, 438661699, 431022084, 423520351, 416153795]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 128).prefactor = (4769753592239139/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 128).cutoff/(generalMeanRows 128).c)).2 =
    (228659234859217/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 128).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 128).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 128).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 128

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 128).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 128).criticalRate j.val*(generalMeanRows 128).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 128).c*(generalMeanRows 128).criticalPoint j.val)).2-
      (generalMeanRows 128).J/2-(generalMeanRows 128).error (generalMeanGrid j.val)+
      (generalMeanRows 128).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 128).c)).2-
      (generalMeanRows 128).J/2-(generalMeanRows 128).error 4 := by
  have he : (generalMeanRows 128).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 128) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 128)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0128

/-! Kernel-checked entropy margins for general spectral rectangle 129. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0129
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5351588233, 5180213594, 5016683649, 4860531015, 4711322145, 4568654364, 4432153236, 4301470191, 4176280403, 4056280870, 3941188684, 3830739466, 3724685941, 3622796650, 3524854769, 3430657036, 3340012768, 3252742965, 3168679482, 3087664272, 3009548693, 2934192862, 2861465068, 2791241225, 2723404366, 2657844182, 2594456583, 2533143305, 2473811532, 2416373557, 2360746461, 2306851811, 2254615389, 2203966929, 2154839880, 2107171180, 2060901046, 2015972782, 1972332593, 1929929418, 1888714767, 1848642575, 1809669059, 1771752590, 1734853570, 1698934316, 1663958955, 1629893318, 1596704850, 1564362520, 1532836734, 1502099262, 1472123160, 1442882700, 1414353310, 1386511506, 1359334840, 1332801841, 1306891965, 1281585551, 1256863768, 1232708577, 1209102692, 1186029536, 1163473212, 1141418462, 1119850641, 1098755685, 1078120079, 1057930836, 1038175467, 1018841957, 999918745, 981394701, 963259106, 945501632, 928112323, 911081580, 894400144, 878059079, 862049760, 846363856, 830993319, 815930371, 801167493, 786697412, 772513090, 758607717, 744974700, 731607651, 718500384, 705646900, 693041386, 680678202, 668551879, 656657106, 644988729, 633541746, 622311292, 611292646, 600481216, 589872539, 579462275, 569246200, 559220206, 549380296, 539722576, 530243256, 520938643, 511805142, 502839246, 494037539, 485396690, 476913452, 468584656, 460407211, 452378103, 444494388, 436753192, 429151711, 421687206]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 129).prefactor = (302073429287381/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 129).cutoff/(generalMeanRows 129).c)).2 =
    (228659234859217/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 129).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 129).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 129).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 129

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 129).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 129).criticalRate j.val*(generalMeanRows 129).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 129).c*(generalMeanRows 129).criticalPoint j.val)).2-
      (generalMeanRows 129).J/2-(generalMeanRows 129).error (generalMeanGrid j.val)+
      (generalMeanRows 129).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 129).c)).2-
      (generalMeanRows 129).J/2-(generalMeanRows 129).error 4 := by
  have he : (generalMeanRows 129).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 129) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 129)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0129

/-! Kernel-checked entropy margins for general spectral rectangle 130. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0130
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5203884046, 5028924302, 4862046675, 4702771539, 4550653896, 4405280350, 4266266405, 4133254046, 4005909559, 3883921570, 3766999281, 3654870859, 3547281988, 3443994544, 3344785392, 3249445286, 3157777867, 3069598741, 2984734638, 2903022636, 2824309450, 2748450775, 2675310685, 2604761071, 2536681127, 2470956876, 2407480724, 2346151054, 2286871845, 2229552320, 2174106618, 2120453494, 2068516026, 2018221362, 1969500466, 1922287892, 1876521572, 1832142611, 1789095104, 1747325962, 1706784746, 1667423516, 1629196687, 1592060898, 1555974881, 1520899351, 1486796888, 1453631836, 1421370211, 1389979600, 1359429085, 1329689154, 1300731632, 1272529605, 1245057358, 1218290305, 1192204935, 1166778755, 1141990236, 1117818764, 1094244596, 1071248809, 1048813265, 1026920570, 1005554034, 984697641, 964336011, 944454373, 925038532, 906074844, 887550188, 869451940, 851767955, 834486536, 817596422, 801086759, 784947090, 769167331, 753737756, 738648980, 723891947, 709457911, 695338425, 681525329, 668010733, 654787012, 641846788, 629182927, 616788520, 604656881, 592781535, 581156209, 569774825, 558631491, 547720495, 537036295, 526573518, 516326947, 506291518, 496462317, 486834568, 477403633, 468165005, 459114304, 450247271, 441559765, 433047757, 424707330, 416534670, 408526064, 400677901, 392986662, 385448920, 378061338, 370820662, 363723725, 356767437, 349948787, 343264839, 336712729, 330289664]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 130).prefactor = (2481279243487107/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 130).cutoff/(generalMeanRows 130).c)).2 =
    (432420918096707/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 130).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 130).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 130).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 130

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 130).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 130).criticalRate j.val*(generalMeanRows 130).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 130).c*(generalMeanRows 130).criticalPoint j.val)).2-
      (generalMeanRows 130).J/2-(generalMeanRows 130).error (generalMeanGrid j.val)+
      (generalMeanRows 130).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 130).c)).2-
      (generalMeanRows 130).J/2-(generalMeanRows 130).error 4 := by
  have he : (generalMeanRows 130).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 130) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 130)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0130

/-! Kernel-checked entropy margins for general spectral rectangle 131. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0131
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5310744673, 5138024557, 4973294197, 4816073139, 4665915932, 4522409060, 4385168210, 4253835817, 4128078860, 4007586870, 3892070142, 3781258104, 3674897843, 3572752767, 3474601380, 3380236167, 3289462581, 3202098102, 3117971390, 3036921493, 2958797130, 2883456023, 2810764287, 2740595864, 2672832001, 2607360767, 2544076608, 2482879930, 2423676719, 2366378183, 2310900420, 2257164115, 2205094249, 2154619837, 2105673680, 2058192130, 2012114880, 1967384759, 1923947549, 1881751805, 1840748694, 1800891841, 1762137188, 1724442857, 1687769025, 1652077809, 1617333155, 1583500732, 1550547838, 1518443309, 1487157434, 1456661872, 1426929580, 1397934744, 1369652706, 1342059908, 1315133831, 1288852940, 1263196632, 1238145185, 1213679718, 1189782139, 1166435112, 1143622015, 1121326904, 1099534477, 1078230045, 1057399500, 1037029287, 1017106376, 997618234, 978552808, 959898493, 941644118, 923778922, 906292535, 889174959, 872416553, 856008015, 839940366, 824204939, 808793359, 793697534, 778909645, 764422126, 750227662, 736319171, 722689800, 709332910, 696242071, 683411051, 670833810, 658504490, 646417408, 634567051, 622948066, 611555258, 600383578, 589428123, 578684129, 568146963, 557812122, 547675224, 537732007, 527978323, 518410137, 509023516, 499814634, 490779760, 481915262, 473217600, 464683321, 456309061, 448091538, 440027552, 432113980, 424347775, 416725963, 409245642, 401903977, 394698202]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 131).prefactor = (4955029358518013/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 131).cutoff/(generalMeanRows 131).c)).2 =
    (461529002254777/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 131).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 131).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 131).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 131

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 131).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 131).criticalRate j.val*(generalMeanRows 131).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 131).c*(generalMeanRows 131).criticalPoint j.val)).2-
      (generalMeanRows 131).J/2-(generalMeanRows 131).error (generalMeanGrid j.val)+
      (generalMeanRows 131).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 131).c)).2-
      (generalMeanRows 131).J/2-(generalMeanRows 131).error 4 := by
  have he : (generalMeanRows 131).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 131) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 131)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0131

/-! Kernel-checked entropy margins for general spectral rectangle 132. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0132
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5186058434, 5011811344, 4845675386, 4687164092, 4535826365, 4391243390, 4253025868, 4120811535, 3994262933, 3873065408, 3756925288, 3645568247, 3538737812, 3436194009, 3337712130, 3243081605, 3152104976, 3064596951, 2980383543, 2899301277, 2821196460, 2745924508, 2673349331, 2603342761, 2535784022, 2470559248, 2407561025, 2346687979, 2287844387, 2230939813, 2175888781, 2122610459, 2071028373, 2021070137, 1972667205, 1925754634, 1880270869, 1836157539, 1793359269, 1751823501, 1711500329, 1672342347, 1634304499, 1597343947, 1561419946, 1526493719, 1492528353, 1459488688, 1427341223, 1396054024, 1365596636, 1335940002, 1307056389, 1278919313, 1251503476, 1224784700, 1198739867, 1173346867, 1148584539, 1124432628, 1100871733, 1077883267, 1055449413, 1033553086, 1012177894, 991308108, 970928625, 951024937, 931583106, 912589730, 894031923, 875897288, 858173891, 840850243, 823915278, 807358333, 791169128, 775337751, 759854640, 744710568, 729896624, 715404206, 701225002, 687350978, 673774368, 660487661, 647483591, 634755126, 622295457, 610097992, 598156344, 586464323, 575015931, 563805351, 552826940, 542075225, 531544894, 521230788, 511127901, 501231368, 491536464, 482038596, 472733299, 463616235, 454683180, 445930028, 437352784, 428947559, 420710567, 412638123, 404726637, 396972612, 389372642, 381923407, 374621672, 367464283, 360448164, 353570316, 346827815, 340217806, 333737506]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 132).prefactor = (1003782245482211/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 132).cutoff/(generalMeanRows 132).c)).2 =
    (27812481268973/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 132).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 132).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 132).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 132

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 132).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 132).criticalRate j.val*(generalMeanRows 132).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 132).c*(generalMeanRows 132).criticalPoint j.val)).2-
      (generalMeanRows 132).J/2-(generalMeanRows 132).error (generalMeanGrid j.val)+
      (generalMeanRows 132).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 132).c)).2-
      (generalMeanRows 132).J/2-(generalMeanRows 132).error 4 := by
  have he : (generalMeanRows 132).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 132) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 132)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0132

/-! Kernel-checked entropy margins for general spectral rectangle 133. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0133
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5161777078, 4988277572, 4822823779, 4664935712, 4514168156, 4370107635, 4232369693, 4100596461, 3974454466, 3853632665, 3737840659, 3626807085, 3520278151, 3418016306, 3319799032, 3225417736, 3134676740, 3047392357, 2963392045, 2882513623, 2804604561, 2729521315, 2657128726, 2587299453, 2519913459, 2454857531, 2392024836, 2331314510, 2272631276, 2215885095, 2160990830, 2107867947, 2056440225, 2006635499, 1958385405, 1911625155, 1866293322, 1822331640, 1779684814, 1738300351, 1698128392, 1659121560, 1621234819, 1584425339, 1548652369, 1513877123, 1480062665, 1447173813, 1415177032, 1384040352, 1353733279, 1324226713, 1295492875, 1267505235, 1240238446, 1213668281, 1187771572, 1162526157, 1137910829, 1113905281, 1090490064, 1067646543, 1045356855, 1023603869, 1002371151, 981642927, 961404054, 941639986, 922336746, 903480897, 885059518, 867060181, 849470921, 832280221, 815476988, 799050534, 782990555, 767287120, 751930645, 736911884, 722221913, 707852112, 693794157, 680040003, 666581872, 653412246, 640523851, 627909647, 615562822, 603476779, 591645129, 580061681, 568720437, 557615578, 546741467, 536092629, 525663758, 515449700, 505445452, 495646156, 486047093, 476643679, 467431455, 458406091, 449563374, 440899206, 432409603, 424090685, 415938679, 407949910, 400120799, 392447863, 384927707, 377557023, 370332591, 363251267, 356309992, 349505777, 342835714, 336296960, 329886747]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 133).prefactor = (2479427123626523/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 133).cutoff/(generalMeanRows 133).c)).2 =
    (219345265555151/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 133).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 133).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 133).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 133

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 133).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 133).criticalRate j.val*(generalMeanRows 133).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 133).c*(generalMeanRows 133).criticalPoint j.val)).2-
      (generalMeanRows 133).J/2-(generalMeanRows 133).error (generalMeanGrid j.val)+
      (generalMeanRows 133).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 133).c)).2-
      (generalMeanRows 133).J/2-(generalMeanRows 133).error 4 := by
  have he : (generalMeanRows 133).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 133) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 133)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0133

/-! Kernel-checked entropy margins for general spectral rectangle 134. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0134
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5195456203, 5020824661, 4854291330, 4695373088, 4543621817, 4398621342, 4259984699, 4127351684, 4000386649, 3878776520, 3762229004, 3650470968, 3543246962, 3440317888, 3341459775, 3246462667, 3155129612, 3067275724, 2982727334, 2901321203, 2822903806, 2747330664, 2674465734, 2604180845, 2536355177, 2470874777, 2407632117, 2346525673, 2287459548, 2230343114, 2175090679, 2121621184, 2069857912, 2019728224, 1971163312, 1924097964, 1878470354, 1834221834, 1791296750, 1749642266, 1709208196, 1669946856, 1631812915, 1594763263, 1558756885, 1523754740, 1489719653, 1456616209, 1424410659, 1393070821, 1362566003, 1332866915, 1303945597, 1275775346, 1248330649, 1221587120, 1195521443, 1170111309, 1145335373, 1121173195, 1097605201, 1074612633, 1052177511, 1030282593, 1008911337, 988047867, 967676942, 947783919, 928354730, 909375852, 890834280, 872717502, 855013477, 837710612, 820797743, 804264111, 788099346, 772293450, 756836778, 741720024, 726934205, 712470645, 698320966, 684477070, 670931129, 657675575, 644703086, 632006578, 619579194, 607414293, 595505445, 583846418, 572431175, 561253861, 550308799, 539590481, 529093564, 518812862, 508743339, 498880106, 489218412, 479753643, 470481312, 461397060, 452496646, 443775948, 435230952, 426857756, 418652561, 410611667, 402731473, 395008473, 387439250, 380020475, 372748905, 365621378, 358634813, 351786203, 345072619, 338491202, 332039164]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 134).prefactor = (4991209358180991/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 134).cutoff/(generalMeanRows 134).c)).2 =
    (219345265555151/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 134).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 134).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 134).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 134

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 134).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 134).criticalRate j.val*(generalMeanRows 134).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 134).c*(generalMeanRows 134).criticalPoint j.val)).2-
      (generalMeanRows 134).J/2-(generalMeanRows 134).error (generalMeanGrid j.val)+
      (generalMeanRows 134).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 134).c)).2-
      (generalMeanRows 134).J/2-(generalMeanRows 134).error 4 := by
  have he : (generalMeanRows 134).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 134) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 134)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0134

/-! Kernel-checked entropy margins for general spectral rectangle 135. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0135
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5054292894, 4879058979, 4711976834, 4552563663, 4400371464, 4254983992, 4116014042, 3983101018, 3855908749, 3734123516, 3617452279, 3505621060, 3398373490, 3295469477, 3196683997, 3101805991, 3010637359, 2922992033, 2838695131, 2757582181, 2679498404, 2604298058, 2531843830, 2462006273, 2394663293, 2329699668, 2267006603, 2206481323, 2148026686, 2091550838, 2036966873, 1984192536, 1933149934, 1883765274, 1835968611, 1789693622, 1744877390, 1701460201, 1659385359, 1618599010, 1579049977, 1540689605, 1503471623, 1467352002, 1432288835, 1398242212, 1365174117, 1333048318, 1301830270, 1271487024, 1241987142, 1213300613, 1185398780, 1158254263, 1131840898, 1106133668, 1081108647, 1056742942, 1033014638, 1009902750, 987387179, 965448659, 944068723, 923229660, 902914477, 883106865, 863791165, 844952337, 826575929, 808648052, 791155347, 774084967, 757424548, 741162190, 725286433, 709786237, 694650965, 679870362, 665434541, 651333963, 637559424, 624102040, 610953233, 598104717, 585548486, 573276802, 561282184, 549557398, 538095443, 526889548, 515933155, 505219917, 494743685, 484498502, 474478595, 464678369, 455092397, 445715418, 436542326, 427568168, 418788136, 410197561, 401791910, 393566781, 385517895, 377641096, 369932344, 362387710, 355003376, 347775626, 340700847, 333775523, 326996232, 320359643, 313862515, 307501690, 301274093, 295176731, 289206684, 283361110, 277637239]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 135).prefactor = (2497720998470379/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 135).cutoff/(generalMeanRows 135).c)).2 =
    (416160397224929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 135).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 135).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 135).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 135

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 135).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 135).criticalRate j.val*(generalMeanRows 135).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 135).c*(generalMeanRows 135).criticalPoint j.val)).2-
      (generalMeanRows 135).J/2-(generalMeanRows 135).error (generalMeanGrid j.val)+
      (generalMeanRows 135).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 135).c)).2-
      (generalMeanRows 135).J/2-(generalMeanRows 135).error 4 := by
  have he : (generalMeanRows 135).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 135) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 135)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0135

/-! Kernel-checked entropy margins for general spectral rectangle 136. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0136
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4998346309, 4822454477, 4654775732, 4494824035, 4342148346, 4196329565, 4056977804, 3923729942, 3796247425, 3674214285, 3557335356, 3445334651, 3337953896, 3234951193, 3136099805, 3041187047, 2950013272, 2862390940, 2778143770, 2697105957, 2619121450, 2544043295, 2471733022, 2402060079, 2334901318, 2270140508, 2207667891, 2147379769, 2089178120, 2032970242, 1978668424, 1926189636, 1875455243, 1826390741, 1778925505, 1732992558, 1688528358, 1645472589, 1603767981, 1563360127, 1524197318, 1486230395, 1449412595, 1413699423, 1379048521, 1345419551, 1312774081, 1281075482, 1250288829, 1220380808, 1191319628, 1163074944, 1135617774, 1108920431, 1082956451, 1057700535, 1033128483, 1009217138, 985944336, 963288853, 941230357, 919749362, 898827190, 878445927, 858588387, 839238076, 820379158, 801996423, 784075258, 766601617, 749561996, 732943405, 716733348, 700919795, 685491164, 670436300, 655744454, 641405267, 627408751, 613745272, 600405537, 587380577, 574661731, 562240638, 550109220, 538259671, 526684445, 515376248, 504328022, 493532943, 482984403, 472676008, 462601566, 452755079, 443130738, 433722912, 424526142, 415535139, 406744768, 398150053, 389746164, 381528411, 373492245, 365633247, 357947126, 350429713, 343076958, 335884925, 328849789, 321967829, 315235430, 308649073, 302205337, 295900893, 289732500, 283697006, 277791340, 272012515, 266357619, 260823819, 255408353]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 136).prefactor = (2514271701814721/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 136).cutoff/(generalMeanRows 136).c)).2 =
    (204064112763831/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 136).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 136).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 136).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 136

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 136).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 136).criticalRate j.val*(generalMeanRows 136).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 136).c*(generalMeanRows 136).criticalPoint j.val)).2-
      (generalMeanRows 136).J/2-(generalMeanRows 136).error (generalMeanGrid j.val)+
      (generalMeanRows 136).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 136).c)).2-
      (generalMeanRows 136).J/2-(generalMeanRows 136).error 4 := by
  have he : (generalMeanRows 136).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 136) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 136)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0136

/-! Kernel-checked entropy margins for general spectral rectangle 137. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0137
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5135883325, 4960532171, 4793340487, 4633822026, 4481525743, 4336032711, 4196953378, 4063925101, 3936609935, 3814692633, 3697878847, 3585893499, 3478479297, 3375395393, 3276416155, 3181330049, 3089938619, 3002055549, 2917505807, 2836124854, 2757757923, 2682259350, 2609491961, 2539326501, 2471641114, 2406320858, 2343257252, 2282347865, 2223495928, 2166609977, 2111603518, 2058394722, 2006906134, 1957064407, 1908800051, 1862047201, 1816743400, 1772829399, 1730248961, 1688948692, 1648877870, 1609988295, 1572234138, 1535571812, 1499959842, 1465358744, 1431730919, 1399040543, 1367253470, 1336337142, 1306260499, 1276993902, 1248509053, 1220778922, 1193777686, 1167480656, 1141864226, 1116905810, 1092583794, 1068877480, 1045767047, 1023233498, 1001258624, 979824963, 958915762, 938514941, 918607063, 899177298, 880211399, 861695669, 843616937, 825962532, 808720261, 791878385, 775425599, 759351009, 743644118, 728294805, 713293307, 698630205, 684296409, 670283140, 656581922, 643184563, 630083147, 617270020, 604737780, 592479265, 580487546, 568755912, 557277868, 546047120, 535057570, 524303308, 513778605, 503477904, 493395813, 483527104, 473866699, 464409671, 455151232, 446086735, 437211663, 428521626, 420012358, 411679710, 403519649, 395528250, 387701695, 380036270, 372528357, 365174437, 357971081, 350914951, 344002796, 337231445, 330597812, 324098888, 317731740, 311493506, 305381400]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 137).prefactor = (1255943894247023/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 137).cutoff/(generalMeanRows 137).c)).2 =
    (215263610235571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 137).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 137).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 137).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 137

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 137).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 137).criticalRate j.val*(generalMeanRows 137).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 137).c*(generalMeanRows 137).criticalPoint j.val)).2-
      (generalMeanRows 137).J/2-(generalMeanRows 137).error (generalMeanGrid j.val)+
      (generalMeanRows 137).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 137).c)).2-
      (generalMeanRows 137).J/2-(generalMeanRows 137).error 4 := by
  have he : (generalMeanRows 137).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 137) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 137)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0137

/-! Kernel-checked entropy margins for general spectral rectangle 138. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0138
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5077498505, 4901465898, 4733653958, 4573573263, 4420769786, 4274821805, 4135337138, 4001950664, 3874322099, 3752133990, 3635089904, 3522912787, 3415343476, 3312139349, 3213073087, 3117931556, 3026514778, 2938634987, 2854115770, 2772791273, 2694505474, 2619111510, 2546471064, 2476453788, 2408936781, 2343804101, 2280946312, 2220260066, 2161647717, 2105016962, 2050280502, 1997355735, 1946164467, 1896632640, 1848690083, 1802270278, 1757310140, 1713749816, 1671532493, 1630604218, 1590913738, 1552412339, 1515053699, 1478793758, 1443590586, 1409404263, 1376196769, 1343931875, 1312575048, 1282093358, 1252455387, 1223631151, 1195592020, 1168310648, 1141760906, 1115917811, 1090757477, 1066257046, 1042394643, 1019149324, 996501025, 974430521, 952919383, 931949936, 911505225, 891568975, 872125562, 853159979, 834657806, 816605184, 798988783, 781795783, 765013848, 748631100, 732636104, 717017841, 701765693, 686869425, 672319166, 658105393, 644218916, 630650865, 617392671, 604436060, 591773033, 579395862, 567297070, 555469428, 543905942, 532599840, 521544567, 510733778, 500161322, 489821242, 479707763, 469815286, 460138382, 450671784, 441410382, 432349215, 423483470, 414808471, 406319677, 398012677, 389883185, 381927034, 374140174, 366518667, 359058684, 351756497, 344608484, 337611115, 330760958, 324054669, 317488995, 311060765, 304766892, 298604368, 292570263, 286661720, 280875956]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 138).prefactor = (2528277140546549/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 138).cutoff/(generalMeanRows 138).c)).2 =
    (105607502559631/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 138).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 138).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 138).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 138

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 138).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 138).criticalRate j.val*(generalMeanRows 138).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 138).c*(generalMeanRows 138).criticalPoint j.val)).2-
      (generalMeanRows 138).J/2-(generalMeanRows 138).error (generalMeanGrid j.val)+
      (generalMeanRows 138).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 138).c)).2-
      (generalMeanRows 138).J/2-(generalMeanRows 138).error 4 := by
  have he : (generalMeanRows 138).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 138) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 138)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0138

/-! Kernel-checked entropy margins for general spectral rectangle 139. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0139
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4943517301, 4767002588, 4598762153, 4438306666, 4285182000, 4138966158, 3999266528, 3865717426, 3737977879, 3615729640, 3498675388, 3386537097, 3279054563, 3175984060, 3077097117, 2982179402, 2891029703, 2803458995, 2719289582, 2638354311, 2560495850, 2485566022, 2413425189, 2343941690, 2276991313, 2212456814, 2150227467, 2090198648, 2032271449, 1976352324, 1922352752, 1870188927, 1819781474, 1771055180, 1723938739, 1678364524, 1634268370, 1591589365, 1550269666, 1510254317, 1471491086, 1433930309, 1397524743, 1362229429, 1328001567, 1294800394, 1262587071, 1231324581, 1200977624, 1171512528, 1142897161, 1115100847, 1088094292, 1061849505, 1036339737, 1011539410, 987424060, 963970279, 941155660, 918958747, 897358987, 876336683, 855872955, 835949695, 816549534, 797655801, 779252493, 761324239, 743856273, 726834406, 710244994, 694074916, 678311549, 662942746, 647956812, 633342484, 619088912, 605185640, 591622589, 578390040, 565478618, 552879276, 540583283, 528582210, 516867913, 505432527, 494268452, 483368339, 472725083, 462331814, 452181882, 442268854, 432586503, 423128797, 413889898, 404864146, 396046059, 387430324, 379011789, 370785458, 362746485, 354890170, 347211950, 339707398, 332372216, 325202229, 318193384, 311341743, 304643479, 298094874, 291692315, 285432286, 279311372, 273326250, 267473689, 261750543, 256153753, 250680342, 245327412, 240092142, 234971784]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 139).prefactor = (1265466037723521/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 139).cutoff/(generalMeanRows 139).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 139).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 139).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 139).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 139

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 139).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 139).criticalRate j.val*(generalMeanRows 139).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 139).c*(generalMeanRows 139).criticalPoint j.val)).2-
      (generalMeanRows 139).J/2-(generalMeanRows 139).error (generalMeanGrid j.val)+
      (generalMeanRows 139).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 139).c)).2-
      (generalMeanRows 139).J/2-(generalMeanRows 139).error 4 := by
  have he : (generalMeanRows 139).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 139) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 139)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0139

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock01 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 1 i) := by
  fin_cases i
  · exact EntropyRow0070.numerical
  · exact EntropyRow0071.numerical
  · exact EntropyRow0072.numerical
  · exact EntropyRow0073.numerical
  · exact EntropyRow0074.numerical
  · exact EntropyRow0075.numerical
  · exact EntropyRow0076.numerical
  · exact EntropyRow0077.numerical
  · exact EntropyRow0078.numerical
  · exact EntropyRow0079.numerical
  · exact EntropyRow0080.numerical
  · exact EntropyRow0081.numerical
  · exact EntropyRow0082.numerical
  · exact EntropyRow0083.numerical
  · exact EntropyRow0084.numerical
  · exact EntropyRow0085.numerical
  · exact EntropyRow0086.numerical
  · exact EntropyRow0087.numerical
  · exact EntropyRow0088.numerical
  · exact EntropyRow0089.numerical
  · exact EntropyRow0090.numerical
  · exact EntropyRow0091.numerical
  · exact EntropyRow0092.numerical
  · exact EntropyRow0093.numerical
  · exact EntropyRow0094.numerical
  · exact EntropyRow0095.numerical
  · exact EntropyRow0096.numerical
  · exact EntropyRow0097.numerical
  · exact EntropyRow0098.numerical
  · exact EntropyRow0099.numerical
  · exact EntropyRow0100.numerical
  · exact EntropyRow0101.numerical
  · exact EntropyRow0102.numerical
  · exact EntropyRow0103.numerical
  · exact EntropyRow0104.numerical
  · exact EntropyRow0105.numerical
  · exact EntropyRow0106.numerical
  · exact EntropyRow0107.numerical
  · exact EntropyRow0108.numerical
  · exact EntropyRow0109.numerical
  · exact EntropyRow0110.numerical
  · exact EntropyRow0111.numerical
  · exact EntropyRow0112.numerical
  · exact EntropyRow0113.numerical
  · exact EntropyRow0114.numerical
  · exact EntropyRow0115.numerical
  · exact EntropyRow0116.numerical
  · exact EntropyRow0117.numerical
  · exact EntropyRow0118.numerical
  · exact EntropyRow0119.numerical
  · exact EntropyRow0120.numerical
  · exact EntropyRow0121.numerical
  · exact EntropyRow0122.numerical
  · exact EntropyRow0123.numerical
  · exact EntropyRow0124.numerical
  · exact EntropyRow0125.numerical
  · exact EntropyRow0126.numerical
  · exact EntropyRow0127.numerical
  · exact EntropyRow0128.numerical
  · exact EntropyRow0129.numerical
  · exact EntropyRow0130.numerical
  · exact EntropyRow0131.numerical
  · exact EntropyRow0132.numerical
  · exact EntropyRow0133.numerical
  · exact EntropyRow0134.numerical
  · exact EntropyRow0135.numerical
  · exact EntropyRow0136.numerical
  · exact EntropyRow0137.numerical
  · exact EntropyRow0138.numerical
  · exact EntropyRow0139.numerical
end SingularValueBounds.KL.Certificates
