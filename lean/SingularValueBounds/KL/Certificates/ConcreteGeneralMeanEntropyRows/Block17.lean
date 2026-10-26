import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 1190. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1190
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7009657781, 6818163006, 6633961054, 6456633299, 6285793776, 6121086088, 5962180666, 5808772308, 5660577994, 5517334916, 5378798716, 5244741897, 5114952395, 4989232286, 4867396619, 4749272364, 4634697448, 4523519891, 4415597013, 4310794715, 4208986828, 4110054511, 4013885706, 3920374645, 3829421385, 3740931400, 3654815189, 3570987935, 3489369171, 3409882495, 3332455287, 3257018468, 3183506259, 3111855977, 3042007830, 2973904742, 2907492179, 2842718001, 2779532309, 2717887319, 2657737236, 2599038140, 2541747876, 2485825961, 2431233487, 2377933037, 2325888607, 2275065529, 2225430404, 2176951033, 2129596363, 2083336425, 2038142283, 1993985986, 1950840517, 1908679756, 1867478432, 1827212092, 1787857056, 1749390393, 1711789882, 1675033983, 1639101809, 1603973104, 1569628207, 1536048039, 1503214075, 1471108320, 1439713297, 1409012018, 1378987973, 1349625110, 1320907816, 1292820908, 1265349609, 1238479544, 1212196716, 1186487501, 1161338634, 1136737192, 1112670591, 1089126569, 1066093179, 1043558775, 1021512010, 999941819, 978837415, 958188279, 937984153, 918215032, 898871154, 879942999, 861421275, 843296917, 825561077, 808205120, 791220618, 774599342, 758333261, 742414531, 726835495, 711588674, 696666766, 682062638, 667769325, 653780020, 640088078, 626687003, 613570452, 600732226, 588166268, 575866660, 563827617, 552043489, 540508751, 529218005, 518165974, 507347500, 496757542, 486391172, 476243571]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1190).prefactor = (3039313265676763/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1190).cutoff/(generalMeanRows 1190).c)).2 =
    (629460917437909/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1190).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1190).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1190).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1190

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1190).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1190).criticalRate j.val*(generalMeanRows 1190).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1190).c*(generalMeanRows 1190).criticalPoint j.val)).2-
      (generalMeanRows 1190).J/2-(generalMeanRows 1190).error (generalMeanGrid j.val)+
      (generalMeanRows 1190).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1190).c)).2-
      (generalMeanRows 1190).J/2-(generalMeanRows 1190).error 4 := by
  have he : (generalMeanRows 1190).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1190) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1190)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1190

/-! Kernel-checked entropy margins for general spectral rectangle 1191. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1191
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5909408068, 5755400629, 5607157437, 5464346969, 5326663569, 5193825015, 5065570345, 4941657921, 4821863698, 4705979665, 4593812456, 4485182088, 4379920836, 4277872204, 4178890005, 4082837522, 3989586750, 3899017703, 3811017791, 3725481247, 3642308607, 3561406235, 3482685887, 3406064321, 3331462924, 3258807388, 3188027402, 3119056369, 3051831153, 2986291842, 2922381526, 2860046104, 2799234093, 2739896459, 2681986462, 2625459509, 2570273021, 2516386304, 2463760443, 2412358186, 2362143851, 2313083233, 2265143517, 2218293202, 2172502025, 2127740895, 2083981825, 2041197877, 1999363105, 1958452505, 1918441961, 1879308208, 1841028785, 1803581995, 1766946871, 1731103140, 1696031189, 1661712038, 1628127308, 1595259197, 1563090451, 1531604345, 1500784656, 1470615645, 1441082035, 1412168995, 1383862117, 1356147406, 1329011259, 1302440450, 1276422120, 1250943760, 1225993197, 1201558585, 1177628393, 1154191392, 1131236644, 1108753497, 1086731570, 1065160745, 1044031162, 1023333205, 1003057499, 983194901, 963736490, 944673566, 925997636, 907700413, 889773810, 872209930, 855001063, 838139682, 821618436, 805430144, 789567792, 774024529, 758793659, 743868643, 729243086, 714910743, 700865505, 687101405, 673612607, 660393406, 647438225, 634741609, 622298224, 610102854, 598150398, 586435867, 574954378, 563701158, 552671535, 541860939, 531264900, 520879043, 510699087, 500720843, 490940210, 481353179, 471955821]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1191).prefactor = (4827558022608169/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1191).cutoff/(generalMeanRows 1191).c)).2 =
    (19807815558021/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1191).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1191).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1191).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1191

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1191).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1191).criticalRate j.val*(generalMeanRows 1191).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1191).c*(generalMeanRows 1191).criticalPoint j.val)).2-
      (generalMeanRows 1191).J/2-(generalMeanRows 1191).error (generalMeanGrid j.val)+
      (generalMeanRows 1191).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1191).c)).2-
      (generalMeanRows 1191).J/2-(generalMeanRows 1191).error 4 := by
  have he : (generalMeanRows 1191).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1191) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1191)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1191

/-! Kernel-checked entropy margins for general spectral rectangle 1192. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1192
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6066706697, 5906527048, 5752371599, 5603894468, 5460776708, 5322723767, 5189463237, 5060742831, 4936328587, 4816003244, 4699564800, 4586825194, 4477609138, 4371753047, 4269104082, 4169519274, 4072864737, 3979014948, 3887852096, 3799265487, 3713151003, 3629410607, 3547951890, 3468687660, 3391535565, 3316417741, 3243260503, 3171994044, 3102552176, 3034872075, 2968894061, 2904561387, 2841820046, 2780618591, 2720907978, 2662641408, 2605774189, 2550263607, 2496068806, 2443150678, 2391471755, 2340996119, 2291689311, 2243518248, 2196451147, 2150457451, 2105507768, 2061573803, 2018628303, 1976645003, 1935598577, 1895464586, 1856219439, 1817840350, 1780305297, 1743592991, 1707682837, 1672554904, 1638189895, 1604569120, 1571674467, 1539488379, 1507993831, 1477174303, 1447013767, 1417496661, 1388607871, 1360332718, 1332656934, 1305566653, 1279048392, 1253089038, 1227675833, 1202796365, 1178438551, 1154590628, 1131241143, 1108378940, 1085993151, 1064073186, 1042608726, 1021589711, 1001006335, 980849033, 961108480, 941775580, 922841457, 904297453, 886135119, 868346207, 850922668, 833856644, 817140462, 800766631, 784727835, 769016928, 753626930, 738551023, 723782546, 709314990, 695141996, 681257348, 667654972, 654328931, 641273422, 628482772, 615951435, 603673987, 591645129, 579859674, 568312554, 556998810, 545913594, 535052163, 524409879, 513982202, 503764696, 493753017, 483942917, 474330240, 464910919]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1192).prefactor = (5026137004061431/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1192).cutoff/(generalMeanRows 1192).c)).2 =
    (628899592696813/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1192).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1192).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1192).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1192

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1192).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1192).criticalRate j.val*(generalMeanRows 1192).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1192).c*(generalMeanRows 1192).criticalPoint j.val)).2-
      (generalMeanRows 1192).J/2-(generalMeanRows 1192).error (generalMeanGrid j.val)+
      (generalMeanRows 1192).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1192).c)).2-
      (generalMeanRows 1192).J/2-(generalMeanRows 1192).error 4 := by
  have he : (generalMeanRows 1192).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1192) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1192)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1192

/-! Kernel-checked entropy margins for general spectral rectangle 1193. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1193
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6141598107, 5975245447, 5815211088, 5661133371, 5512678686, 5369538831, 5231428669, 5098084030, 4969259838, 4844728429, 4724278041, 4607711458, 4494844782, 4385506328, 4279535624, 4176782502, 4077106281, 3980375013, 3886464810, 3795259223, 3706648678, 3620529962, 3536805750, 3455384179, 3376178454, 3299106481, 3224090546, 3151057001, 3079935991, 3010661197, 2943169595, 2877401243, 2813299079, 2750808733, 2689878359, 2630458477, 2572501822, 2515963216, 2460799437, 2406969103, 2354432567, 2303151817, 2253090378, 2204213233, 2156486734, 2109878536, 2064357521, 2019893734, 1976458325, 1934023489, 1892562416, 1852049238, 1812458986, 1773767545, 1735951614, 1698988666, 1662856915, 1627535280, 1593003354, 1559241376, 1526230200, 1493951272, 1462386602, 1431518741, 1401330761, 1371806233, 1342929207, 1314684191, 1287056139, 1260030428, 1233592846, 1207729576, 1182427178, 1157672584, 1133453075, 1109756275, 1086570138, 1063882936, 1041683247, 1019959948, 998702203, 977899454, 957541413, 937618052, 918119596, 899036515, 880359516, 862079536, 844187736, 826675493, 809534393, 792756228, 776332988, 760256854, 744520196, 729115564, 714035686, 699273461, 684821956, 670674401, 656824182, 643264841, 629990069, 616993704, 604269725, 591812249, 579615528, 567673948, 555982019, 544534378, 533325782, 522351109, 511605350, 501083611, 490781104, 480693153, 470815184, 461142723, 451671400, 442396939, 433315159]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1193).prefactor = (5232884424234713/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1193).cutoff/(generalMeanRows 1193).c)).2 =
    (619071503760551/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1193).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1193).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1193).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1193

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1193).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1193).criticalRate j.val*(generalMeanRows 1193).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1193).c*(generalMeanRows 1193).criticalPoint j.val)).2-
      (generalMeanRows 1193).J/2-(generalMeanRows 1193).error (generalMeanGrid j.val)+
      (generalMeanRows 1193).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1193).c)).2-
      (generalMeanRows 1193).J/2-(generalMeanRows 1193).error 4 := by
  have he : (generalMeanRows 1193).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1193) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1193)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1193

/-! Kernel-checked entropy margins for general spectral rectangle 1194. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1194
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6305326677, 6132386082, 5966047105, 5805932383, 5651693757, 5503009530, 5359582028, 5221135413, 5087413740, 4958179202, 4833210566, 4712301751, 4595260559, 4481907523, 4372074864, 4265605548, 4162352431, 4062177480, 3964951071, 3870551336, 3778863585, 3689779764, 3603197970, 3519021998, 3437160935, 3357528784, 3280044116, 3204629755, 3131212489, 3059722801, 2990094620, 2922265098, 2856174398, 2791765503, 2728984035, 2667778093, 2608098097, 2549896648, 2493128401, 2437749937, 2383719656, 2330997669, 2279545702, 2229327009, 2180306281, 2132449574, 2085724232, 2040098824, 1995543073, 1952027805, 1909524888, 1868007180, 1827448485, 1787823504, 1749107793, 1711277724, 1674310445, 1638183849, 1602876536, 1568367787, 1534637528, 1501666311, 1469435279, 1437926147, 1407121178, 1377003159, 1347555381, 1318761622, 1290606124, 1263073579, 1236149108, 1209818251, 1184066947, 1158881520, 1134248669, 1110155452, 1086589273, 1063537872, 1040989313, 1018931973, 997354532, 976245964, 955595526, 935392749, 915627432, 896289631, 877369651, 858858041, 840745583, 823023289, 805682392, 788714339, 772110786, 755863592, 739964813, 724406695, 709181671, 694282356, 679701538, 665432179, 651467404, 637800504, 624424924, 611334265, 598522274, 585982847, 573710019, 561697965, 549940993, 538433541, 527170178, 516145594, 505354601, 494792130, 484453226, 474333049, 464426865, 454730049, 445238080, 435946538, 426851104]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1194).prefactor = (5448136287425327/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1194).cutoff/(generalMeanRows 1194).c)).2 =
    (307096722653561/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1194).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1194).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1194).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1194

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1194).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1194).criticalRate j.val*(generalMeanRows 1194).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1194).c*(generalMeanRows 1194).criticalPoint j.val)).2-
      (generalMeanRows 1194).J/2-(generalMeanRows 1194).error (generalMeanGrid j.val)+
      (generalMeanRows 1194).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1194).c)).2-
      (generalMeanRows 1194).J/2-(generalMeanRows 1194).error 4 := by
  have he : (generalMeanRows 1194).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1194) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1194)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1194

/-! Kernel-checked entropy margins for general spectral rectangle 1195. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1195
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6564692871, 6384638458, 6211457217, 6044756263, 5884173115, 5729372843, 5580045528, 5435903987, 5296681745, 5162131215, 5032022062, 4906139728, 4784284110, 4666268359, 4551917793, 4441068919, 4333568541, 4229272948, 4128047183, 4029764366, 3934305089, 3841556854, 3751413564, 3663775059, 3578546687, 3495638910, 3414966952, 3336450462, 3260013217, 3185582839, 3113090540, 3042470888, 2973661583, 2906603263, 2841239314, 2777515698, 2715380798, 2654785264, 2595681886, 2538025459, 2481772671, 2426881994, 2373313579, 2321029167, 2269991997, 2220166730, 2171519367, 2124017183, 2077628656, 2032323411, 1988072158, 1944846642, 1902619588, 1861364655, 1821056394, 1781670205, 1743182297, 1705569653, 1668809993, 1632881745, 1597764011, 1563436540, 1529879702, 1497074459, 1465002344, 1433645437, 1402986341, 1373008166, 1343694507, 1315029425, 1286997431, 1259583469, 1232772898, 1206551483, 1180905373, 1155821095, 1131285534, 1107285926, 1083809844, 1060845187, 1038380170, 1016403312, 994903429, 973869623, 953291270, 933158019, 913459776, 894186700, 875329197, 856877906, 838823700, 821157676, 803871145, 786955631, 770402864, 754204771, 738353475, 722841284, 707660692, 692804371, 678265163, 664036082, 650110305, 636481168, 623142163, 610086933, 597309270, 584803106, 572562517, 560581713, 548855037, 537376963, 526142088, 515145136, 504380947, 493844482, 483530812, 473435123, 463552707, 453878963, 444409392]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1195).prefactor = (5672242419285131/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1195).cutoff/(generalMeanRows 1195).c)).2 =
    (307096722653561/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1195).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1195).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1195).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1195

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1195).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1195).criticalRate j.val*(generalMeanRows 1195).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1195).c*(generalMeanRows 1195).criticalPoint j.val)).2-
      (generalMeanRows 1195).J/2-(generalMeanRows 1195).error (generalMeanGrid j.val)+
      (generalMeanRows 1195).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1195).c)).2-
      (generalMeanRows 1195).J/2-(generalMeanRows 1195).error 4 := by
  have he : (generalMeanRows 1195).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1195) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1195)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1195

/-! Kernel-checked entropy margins for general spectral rectangle 1196. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1196
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6739789622, 6552631653, 6372654457, 6199448071, 6032634197, 5871863229, 5716811610, 5567179466, 5422688499, 5283080087, 5148113585, 5017564793, 4891224573, 4768897605, 4650401254, 4535564553, 4424227270, 4316239071, 4211458749, 4109753529, 4010998430, 3915075685, 3821874210, 3731289119, 3643221276, 3557576891, 3474267147, 3393207851, 3314319124, 3237525107, 3162753697, 3089936297, 3019007589, 2949905330, 2882570151, 2816945380, 2752976879, 2690612889, 2629803886, 2570502453, 2512663153, 2456242419, 2401198448, 2347491102, 2295081816, 2243933514, 2194010529, 2145278530, 2097704451, 2051256429, 2005903742, 1961616752, 1918366854, 1876126425, 1834868778, 1794568119, 1755199505, 1716738805, 1679162668, 1642448484, 1606574352, 1571519055, 1537262025, 1503783322, 1471063605, 1439084106, 1407826613, 1377273444, 1347407430, 1318211890, 1289670619, 1261767868, 1234488326, 1207817106, 1181739730, 1156242113, 1131310553, 1106931713, 1083092613, 1059780616, 1036983418, 1014689035, 992885795, 971562328, 950707553, 930310675, 910361171, 890848784, 871763515, 853095613, 834835573, 816974123, 799502219, 782411040, 765691982, 749336648, 733336845, 717684579, 702372049, 687391639, 672735916, 658397624, 644369681, 630645169, 617217338, 604079592, 591225494, 578648754, 566343232, 554302930, 542521988, 530994683, 519715424, 508678749, 497879321, 487311928, 476971475, 466852984, 456951590, 447262542, 437781194]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1196).prefactor = (5905567035354501/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1196).cutoff/(generalMeanRows 1196).c)).2 =
    (609339066842321/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1196).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1196).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1196).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1196

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1196).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1196).criticalRate j.val*(generalMeanRows 1196).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1196).c*(generalMeanRows 1196).criticalPoint j.val)).2-
      (generalMeanRows 1196).J/2-(generalMeanRows 1196).error (generalMeanGrid j.val)+
      (generalMeanRows 1196).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1196).c)).2-
      (generalMeanRows 1196).J/2-(generalMeanRows 1196).error 4 := by
  have he : (generalMeanRows 1196).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1196) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1196)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1196

/-! Kernel-checked entropy margins for general spectral rectangle 1197. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1197
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6364872052, 6172927437, 5988624609, 5811529687, 5641241849, 5477390250, 5319631276, 5167646098, 5021138478, 4879832799, 4743472304, 4611817499, 4484644720, 4361744839, 4242922085, 4127992986, 4016785398, 3909137635, 3804897661, 3703922371, 3606076923, 3511234133, 3419273917, 3330082790, 3243553394, 3159584076, 3078078496, 2998945263, 2922097608, 2847453078, 2774933253, 2704463489, 2635972678, 2569393027, 2504659851, 2441711390, 2380488625, 2320935124, 2262996884, 2206622198, 2151761519, 2098367340, 2046394086, 1995798005, 1946537068, 1898570885, 1851860615, 1806368885, 1762059720, 1718898472, 1676851753, 1635887374, 1595974293, 1557082552, 1519183237, 1482248420, 1446251124, 1411165274, 1376965662, 1343627905, 1311128415, 1279444361, 1248553642, 1218434852, 1189067259, 1160430770, 1132505913, 1105273808, 1078716147, 1052815172, 1027553654, 1002914874, 978882603, 955441086, 932575024, 910269561, 888510262, 867283105, 846574465, 826371098, 806660132, 787429052, 768665690, 750358212, 732495110, 715065188, 698057556, 681461617, 665267060, 649463850, 634042221, 618992667, 604305931, 589973006, 575985118, 562333724, 549010506, 536007362, 523316402, 510929938, 498840482, 487040742, 475523608, 464282159, 453309645, 442599492, 432145293, 421940804, 411979938, 402256764, 392765500, 383500510, 374456299, 365627512, 357008926, 348595451, 340382123, 332364102, 324536669, 316895221, 309435272]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1197).prefactor = (6148489332982543/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1197).cutoff/(generalMeanRows 1197).c)).2 =
    (57600264657473/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1197).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1197).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1197).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1197

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1197).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1197).criticalRate j.val*(generalMeanRows 1197).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1197).c*(generalMeanRows 1197).criticalPoint j.val)).2-
      (generalMeanRows 1197).J/2-(generalMeanRows 1197).error (generalMeanGrid j.val)+
      (generalMeanRows 1197).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1197).c)).2-
      (generalMeanRows 1197).J/2-(generalMeanRows 1197).error 4 := by
  have he : (generalMeanRows 1197).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1197) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1197)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1197

/-! Kernel-checked entropy margins for general spectral rectangle 1198. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1198
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6909041097, 6707752868, 6514350443, 6328385320, 6149443366, 5977141601, 5811125339, 5651065634, 5496656995, 5347615333, 5203676124, 5064592747, 4930134993, 4800087711, 4674249586, 4552432034, 4434458197, 4320162027, 4209387457, 4101987646, 3997824286, 3896766972, 3798692627, 3703484973, 3611034048, 3521235767, 3433991509, 3349207747, 3266795706, 3186671041, 3108753555, 3032966919, 2959238435, 2887498800, 2817681896, 2749724599, 2683566589, 2619150190, 2556420211, 2495323802, 2435810320, 2377831203, 2321339858, 2266291548, 2212643294, 2160353783, 2109383278, 2059693535, 2011247732, 1964010393, 1917947322, 1873025543, 1829213239, 1786479696, 1744795256, 1704131264, 1664460025, 1625754760, 1587989566, 1551139378, 1515179934, 1480087739, 1445840036, 1412414773, 1379790577, 1347946724, 1316863116, 1286520258, 1256899231, 1227981671, 1199749751, 1172186161, 1145274085, 1118997189, 1093339598, 1068285886, 1043821056, 1019930527, 996600120, 973816044, 951564883, 929833585, 908609448, 887880113, 867633546, 847858034, 828542174, 809674862, 791245281, 773242900, 755657457, 738478958, 721697663, 705304084, 689288973, 673643317, 658358333, 643425459, 628836348, 614582863, 600657069, 587051231, 573757805, 560769435, 548078945, 535679339, 523563790, 511725642, 500158399, 488855725, 477811439, 467019509, 456474050, 446169322, 436099720, 426259776, 416644154, 407247648, 398065172, 389091768, 380322593]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1198).prefactor = (6401404107595709/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1198).cutoff/(generalMeanRows 1198).c)).2 =
    (23606153044839/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1198).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1198).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1198).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1198

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1198).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1198).criticalRate j.val*(generalMeanRows 1198).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1198).c*(generalMeanRows 1198).criticalPoint j.val)).2-
      (generalMeanRows 1198).J/2-(generalMeanRows 1198).error (generalMeanGrid j.val)+
      (generalMeanRows 1198).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1198).c)).2-
      (generalMeanRows 1198).J/2-(generalMeanRows 1198).error 4 := by
  have he : (generalMeanRows 1198).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1198) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1198)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1198

/-! Kernel-checked entropy margins for general spectral rectangle 1199. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1199
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7589950883, 7381776002, 7181547731, 6988811820, 6803149180, 6624172573, 6451523676, 6284870454, 6123904815, 5968340506, 5817911216, 5672368881, 5531482145, 5395034976, 5262825413, 5134664427, 5010374897, 4889790669, 4772755706, 4659123314, 4548755436, 4441522003, 4337300351, 4235974674, 4137435538, 4041579424, 3948308312, 3857529305, 3769154274, 3683099538, 3599285566, 3517636705, 3438080928, 3360549600, 3284977266, 3211301448, 3139462468, 3069403269, 3001069266, 2934408197, 2869369984, 2805906611, 2743972010, 2683521943, 2624513911, 2566907053, 2510662062, 2455741100, 2402107723, 2349726814, 2298564507, 2248588133, 2199766158, 2152068129, 2105464620, 2059927191, 2015428334, 1971941437, 1929440741, 1887901305, 1847298968, 1807610315, 1768812650, 1730883963, 1693802902, 1657548748, 1622101388, 1587441294, 1553549498, 1520407572, 1487997608, 1456302198, 1425304417, 1394987804, 1365336347, 1336334465, 1307966999, 1280219190, 1253076669, 1226525447, 1200551898, 1175142747, 1150285064, 1125966248, 1102174018, 1078896404, 1056121736, 1033838638, 1012036014, 990703045, 969829177, 949404115, 929417815, 909860477, 890722538, 871994666, 853667752, 835732905, 818181444, 801004898, 784194992, 767743647, 751642976, 735885273, 720463014, 705368850, 690595601, 676136255, 661983960, 648132023, 634573903, 621303210, 608313699, 595599269, 583153956, 570971930, 559047497, 547375087, 535949259, 524764692, 513816187]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1199).prefactor = (1311623931307417/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1199).cutoff/(generalMeanRows 1199).c)).2 =
    (307096722653561/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1199).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1199).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1199).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1199

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1199).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1199).criticalRate j.val*(generalMeanRows 1199).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1199).c*(generalMeanRows 1199).criticalPoint j.val)).2-
      (generalMeanRows 1199).J/2-(generalMeanRows 1199).error (generalMeanGrid j.val)+
      (generalMeanRows 1199).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1199).c)).2-
      (generalMeanRows 1199).J/2-(generalMeanRows 1199).error 4 := by
  have he : (generalMeanRows 1199).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1199) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1199)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1199

/-! Kernel-checked entropy margins for general spectral rectangle 1200. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1200
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6069238942, 5893407627, 5724373576, 5561750338, 5405181596, 5254338297, 5108916092, 4968633059, 4833227668, 4702456955, 4576094893, 4453930919, 4335768615, 4221424520, 4110727046, 4003515515, 3899639275, 3798956903, 3701335478, 3606649928, 3514782426, 3425621850, 3339063280, 3255007547, 3173360819, 3094034219, 3016943476, 2942008614, 2869153648, 2798306327, 2729397879, 2662362788, 2597138585, 2533665653, 2471887050, 2411748346, 2353197471, 2296184574, 2240661892, 2186583632, 2133905859, 2082586389, 2032584698, 1983861827, 1936380304, 1890104061, 1844998366, 1801029753, 1758165959, 1716375867, 1675629448, 1635897711, 1597152655, 1559367221, 1522515253, 1486571454, 1451511353, 1417311263, 1383948255, 1351400120, 1319645343, 1288663073, 1258433099, 1228935820, 1200152227, 1172063876, 1144652868, 1117901831, 1091793895, 1066312679, 1041442272, 1017167216, 993472488, 970343489, 947766028, 925726305, 904210904, 883206773, 862701221, 842681897, 823136785, 804054192, 785422737, 767231343, 749469225, 732125884, 715191095, 698654902, 682507609, 666739769, 651342182, 636305885, 621622145, 607282452, 593278514, 579602250, 566245784, 553201441, 540461736, 528019376, 515867250, 503998425, 492406140, 481083806, 470024993, 459223436, 448673021, 438367786, 428301918, 418469746, 408865738, 399484497, 390320759, 381369390, 372625380, 364083841, 355740003, 347589214, 339626933, 331848730, 324250283]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1200).prefactor = (5689096007580301/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1200).cutoff/(generalMeanRows 1200).c)).2 =
    (496618313427/781250000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1200).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1200).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1200).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1200

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1200).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1200).criticalRate j.val*(generalMeanRows 1200).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1200).c*(generalMeanRows 1200).criticalPoint j.val)).2-
      (generalMeanRows 1200).J/2-(generalMeanRows 1200).error (generalMeanGrid j.val)+
      (generalMeanRows 1200).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1200).c)).2-
      (generalMeanRows 1200).J/2-(generalMeanRows 1200).error 4 := by
  have he : (generalMeanRows 1200).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1200) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1200)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1200

/-! Kernel-checked entropy margins for general spectral rectangle 1201. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1201
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6201936043, 6020191027, 5845510948, 5677494377, 5515771126, 5359999269, 5209862501, 5065067769, 4925343170, 4790436061, 4660111369, 4534150065, 4412347802, 4294513675, 4180469110, 4070046858, 3963090080, 3859451523, 3758992768, 3661583547, 3567101125, 3475429733, 3386460051, 3300088741, 3216218011, 3134755227, 3055612547, 2978706597, 2903958160, 2831291905, 2760636124, 2691922501, 2625085894, 2560064132, 2496797837, 2435230243, 2375307050, 2316976270, 2260188094, 2204894768, 2151050476, 2098611234, 2047534786, 1997780513, 1949309348, 1902083692, 1856067340, 1811225411, 1767524282, 1724931525, 1683415853, 1642947061, 1603495982, 1565034432, 1527535173, 1490971865, 1455319031, 1420552016, 1386646957, 1353580743, 1321330992, 1289876016, 1259194794, 1229266948, 1200072715, 1171592926, 1143808982, 1116702833, 1090256958, 1064454346, 1039278477, 1014713305, 990743241, 967353138, 944528276, 922254344, 900517432, 879304014, 858600936, 838395404, 818674972, 799427532, 780641304, 762304822, 744406929, 726936762, 709883750, 693237600, 676988288, 661126056, 645641399, 630525061, 615768025, 601361509, 587296956, 573566030, 560160609, 547072780, 534294829, 521819240, 509638690, 497746037, 486134324, 474796765, 463726750, 452917830, 442363720, 432058292, 421995570, 412169729, 402575087, 393206103, 384057374, 375123631, 366399734, 357880671, 349561551, 341437608, 333504188, 325756753, 318190877]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1201).prefactor = (5894401921836893/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1201).cutoff/(generalMeanRows 1201).c)).2 =
    (631041803287817/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1201).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1201).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1201).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1201

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1201).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1201).criticalRate j.val*(generalMeanRows 1201).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1201).c*(generalMeanRows 1201).criticalPoint j.val)).2-
      (generalMeanRows 1201).J/2-(generalMeanRows 1201).error (generalMeanGrid j.val)+
      (generalMeanRows 1201).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1201).c)).2-
      (generalMeanRows 1201).J/2-(generalMeanRows 1201).error 4 := by
  have he : (generalMeanRows 1201).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1201) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1201)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1201

/-! Kernel-checked entropy margins for general spectral rectangle 1202. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1202
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6698050177, 6508472138, 6326142729, 6150649204, 5981611136, 5818677332, 5661523081, 5509847710, 5363372393, 5221838193, 5085004311, 4952646502, 4824555662, 4700536545, 4580406612, 4463994983, 4351141495, 4241695848, 4135516823, 4032471578, 3932435007, 3835289154, 3740922680, 3649230374, 3560112712, 3473475448, 3389229241, 3307289315, 3227575147, 3150010178, 3074521547, 3001039854, 2929498932, 2859835640, 2791989678, 2725903406, 2661521686, 2598791732, 2537662967, 2478086902, 2420017008, 2363408615, 2308218803, 2254406306, 2201931430, 2150755962, 2100843102, 2052157381, 2004664604, 1958331779, 1913127066, 1869019715, 1825980020, 1783979269, 1742989698, 1702984449, 1663937532, 1625823784, 1588618837, 1552299082, 1516841640, 1482224330, 1448425642, 1415424713, 1383201297, 1351735743, 1321008976, 1291002470, 1261698233, 1233078782, 1205127131, 1177826768, 1151161642, 1125116145, 1099675097, 1074823736, 1050547695, 1026832997, 1003666041, 981033587, 958922745, 937320966, 916216032, 895596040, 875449401, 855764822, 836531303, 817738126, 799374847, 781431286, 763897523, 746763888, 730020954, 713659531, 697670658, 682045599, 666775833, 651853051, 637269148, 623016221, 609086559, 595472640, 582167127, 569162862, 556452858, 544030301, 531888541, 520021086, 508421605, 497083915, 486001984, 475169924, 464581986, 454232561, 444116172, 434227473, 424561243, 415112388, 405875931, 396847016, 388020899]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1202).prefactor = (6107116837167217/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1202).cutoff/(generalMeanRows 1202).c)).2 =
    (322497759030841/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1202).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1202).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1202).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1202

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1202).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1202).criticalRate j.val*(generalMeanRows 1202).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1202).c*(generalMeanRows 1202).criticalPoint j.val)).2-
      (generalMeanRows 1202).J/2-(generalMeanRows 1202).error (generalMeanGrid j.val)+
      (generalMeanRows 1202).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1202).c)).2-
      (generalMeanRows 1202).J/2-(generalMeanRows 1202).error 4 := by
  have he : (generalMeanRows 1202).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1202) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1202)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1202

/-! Kernel-checked entropy margins for general spectral rectangle 1203. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1203
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7234566408, 7037047793, 6846960344, 6663879585, 6487414492, 6317204289, 6152915591, 5994239868, 5840891171, 5692604102, 5549131990, 5410245261, 5275729958, 5145386424, 5019028094, 4896480423, 4777579902, 4662173171, 4550116215, 4441273634, 4335517973, 4232729123, 4132793766, 4035604869, 3941061228, 3849067047, 3759531550, 3672368633, 3587496538, 3504837555, 3424317755, 3345866733, 3269417384, 3194905685, 3122270503, 3051453414, 2982398534, 2915052370, 2849363672, 2785283304, 2722764122, 2661760862, 2602230030, 2544129809, 2487419968, 2432061774, 2378017918, 2325252438, 2273730653, 2223419098, 2174285464, 2126298543, 2079428176, 2033645204, 1988921421, 1945229532, 1902543113, 1860836572, 1820085113, 1780264704, 1741352042, 1703324527, 1666160233, 1629837877, 1594336799, 1559636935, 1525718797, 1492563448, 1460152485, 1428468016, 1397492646, 1367209455, 1337601986, 1308654225, 1280350588, 1252675905, 1225615411, 1199154724, 1173279843, 1147977126, 1123233286, 1099035376, 1075370779, 1052227201, 1029592655, 1007455458, 985804219, 964627828, 943915454, 923656531, 903840755, 884458072, 865498674, 846952992, 828811688, 811065650, 793705984, 776724009, 760111254, 743859446, 727960511, 712406565, 697189911, 682303032, 667738589, 653489414, 639548506, 625909028, 612564301, 599507803, 586733161, 574234151, 562004689, 550038835, 538330784, 526874862, 515665529, 504697367, 493965084, 483463509, 473187587]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1203).prefactor = (6327508126759771/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1203).cutoff/(generalMeanRows 1203).c)).2 =
    (26365867904317/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1203).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1203).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1203).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1203

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1203).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1203).criticalRate j.val*(generalMeanRows 1203).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1203).c*(generalMeanRows 1203).criticalPoint j.val)).2-
      (generalMeanRows 1203).J/2-(generalMeanRows 1203).error (generalMeanGrid j.val)+
      (generalMeanRows 1203).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1203).c)).2-
      (generalMeanRows 1203).J/2-(generalMeanRows 1203).error 4 := by
  have he : (generalMeanRows 1203).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1203) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1203)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1203

/-! Kernel-checked entropy margins for general spectral rectangle 1204. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1204
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6128387391, 5964538544, 5806808766, 5654848618, 5508336116, 5366974110, 5230487956, 5098623434, 4971144900, 4847833616, 4728486264, 4612913603, 4500939266, 4392398671, 4287138040, 4185013509, 4085890324, 3989642117, 3896150235, 3805303145, 3716995885, 3631129562, 3547610901, 3466351827, 3387269086, 3310283897, 3235321635, 3162311537, 3091186440, 3021882528, 2954339112, 2888498421, 2824305409, 2761707582, 2700654832, 2641099290, 2582995189, 2526298730, 2470967971, 2416962712, 2364244395, 2312776013, 2262522017, 2213448239, 2165521814, 2118711114, 2072985676, 2028316147, 1984674224, 1942032602, 1900364925, 1859645737, 1819850443, 1780955264, 1742937202, 1705774004, 1669444125, 1633926704, 1599201524, 1565248994, 1532050117, 1499586467, 1467840166, 1436793860, 1406430700, 1376734325, 1347688835, 1319278782, 1291489150, 1264305338, 1237713145, 1211698759, 1186248738, 1161350002, 1136989819, 1113155790, 1089835844, 1067018221, 1044691467, 1022844420, 1001466204, 980546217, 960074124, 940039851, 920433572, 901245706, 882466908, 864088061, 846100270, 828494859, 811263357, 794397502, 777889225, 761730653, 745914098, 730432055, 715277196, 700442365, 685920573, 671704995, 657788963, 644165967, 630829643, 617773778, 604992299, 592479272, 580228901, 568235519, 556493590, 544997703, 533742570, 522723020, 511934001, 501370574, 491027909, 480901286, 470986090, 461277809, 451772029, 442464437, 433350815]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1204).prefactor = (2599039430481023/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1204).cutoff/(generalMeanRows 1204).c)).2 =
    (653655432126967/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1204).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1204).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1204).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1204

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1204).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1204).criticalRate j.val*(generalMeanRows 1204).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1204).c*(generalMeanRows 1204).criticalPoint j.val)).2-
      (generalMeanRows 1204).J/2-(generalMeanRows 1204).error (generalMeanGrid j.val)+
      (generalMeanRows 1204).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1204).c)).2-
      (generalMeanRows 1204).J/2-(generalMeanRows 1204).error 4 := by
  have he : (generalMeanRows 1204).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1204) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1204)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1204

/-! Kernel-checked entropy margins for general spectral rectangle 1205. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1205
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6305239557, 6134555904, 5970279676, 5812045471, 5659516532, 5512382018, 5370354575, 5233168173, 5100576164, 4972349558, 4848275461, 4728155681, 4611805474, 4499052404, 4389735321, 4283703437, 4180815486, 4080938962, 3983949429, 3889729894, 3798170237, 3709166686, 3622621346, 3538441764, 3456540532, 3376834927, 3299246576, 3223701151, 3150128095, 3078460360, 3008634173, 2940588820, 2874266447, 2809611873, 2746572424, 2685097773, 2625139798, 2566652448, 2509591616, 2453915030, 2399582141, 2346554028, 2294793307, 2244264042, 2194931672, 2146762930, 2099725782, 2053789359, 2008923896, 1965100683, 1922292003, 1880471095, 1839612098, 1799690015, 1760680670, 1722560674, 1685307383, 1648898875, 1613313907, 1578531897, 1544532889, 1511297528, 1478807039, 1447043201, 1415988325, 1385625234, 1355937244, 1326908142, 1298522174, 1270764024, 1243618799, 1217072014, 1191109578, 1165717781, 1140883278, 1116593082, 1092834544, 1069595350, 1046863506, 1024627328, 1002875431, 981596722, 960780391, 940415900, 920492974, 901001599, 881932005, 863274668, 845020297, 827159827, 809684418, 792585442, 775854481, 759483319, 743463938, 727788512, 712449402, 697439148, 682750470, 668376257, 654309567, 640543620, 627071795, 613887625, 600984792, 588357128, 575998605, 563903333, 552065560, 540479665, 529140155, 518041664, 507178948, 496546880, 486140453, 475954771, 465985049, 456226610, 446674883, 437325400, 428173792]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1205).prefactor = (5422766042552667/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1205).cutoff/(generalMeanRows 1205).c)).2 =
    (648870734003627/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1205).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1205).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1205).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1205

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1205).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1205).criticalRate j.val*(generalMeanRows 1205).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1205).c*(generalMeanRows 1205).criticalPoint j.val)).2-
      (generalMeanRows 1205).J/2-(generalMeanRows 1205).error (generalMeanGrid j.val)+
      (generalMeanRows 1205).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1205).c)).2-
      (generalMeanRows 1205).J/2-(generalMeanRows 1205).error 4 := by
  have he : (generalMeanRows 1205).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1205) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1205)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1205

/-! Kernel-checked entropy margins for general spectral rectangle 1206. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1206
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6487269176, 6309490897, 6138421413, 5973678614, 5814910283, 5661791248, 5514020851, 5371320690, 5233432601, 5100116853, 4971150524, 4846326047, 4725449899, 4608341415, 4494831724, 4384762781, 4277986493, 4174363924, 4073764577, 3976065736, 3881151873, 3788914103, 3699249689, 3612061587, 3527258038, 3444752185, 3364461725, 3286308597, 3210218685, 3136121554, 3063950199, 2993640824, 2925132630, 2858367625, 2793290444, 2729848186, 2667990266, 2607668270, 2548835829, 2491448499, 2435463649, 2380840356, 2327539314, 2275522741, 2224754297, 2175199008, 2126823195, 2079594402, 2033481343, 1988453833, 1944482742, 1901539938, 1859598245, 1818631392, 1778613977, 1739521423, 1701329944, 1664016508, 1627558807, 1591935225, 1557124806, 1523107231, 1489862792, 1457372363, 1425617382, 1394579827, 1364242194, 1334587480, 1305599164, 1277261186, 1249557935, 1222474230, 1195995305, 1170106798, 1144794730, 1120045500, 1095845867, 1072182940, 1049044166, 1026417322, 1004290498, 982652093, 961490805, 940795617, 920555793, 900760868, 881400639, 862465159, 843944728, 825829885, 808111404, 790780286, 773827749, 757245228, 741024364, 725157002, 709635182, 694451135, 679597280, 665066214, 650850712, 636943721, 623338352, 610027882, 597005742, 584265522, 571800957, 559605932, 547674473, 536000744, 524579045, 513403808, 502469594, 491771087, 481303096, 471060548, 461038484, 451232063, 441636549, 432247319, 423059851]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1206).prefactor = (1414291334299797/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1206).cutoff/(generalMeanRows 1206).c)).2 =
    (80513602530423/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1206).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1206).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1206).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1206

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1206).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1206).criticalRate j.val*(generalMeanRows 1206).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1206).c*(generalMeanRows 1206).criticalPoint j.val)).2-
      (generalMeanRows 1206).J/2-(generalMeanRows 1206).error (generalMeanGrid j.val)+
      (generalMeanRows 1206).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1206).c)).2-
      (generalMeanRows 1206).J/2-(generalMeanRows 1206).error 4 := by
  have he : (generalMeanRows 1206).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1206) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1206)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1206

/-! Kernel-checked entropy margins for general spectral rectangle 1207. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1207
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6674629881, 6489487740, 6311369331, 6139875061, 5974636532, 5815313571, 5661591593, 5513179244, 5369806299, 5231221781, 5097192264, 4967500360, 4841943351, 4720331952, 4602489201, 4488249449, 4377457451, 4269967531, 4165642840, 4064354666, 3965981813, 3870410036, 3777531524, 3687244424, 3599452414, 3514064303, 3430993676, 3350158554, 3271481095, 3194887313, 3120306820, 3047672589, 2976920738, 2907990328, 2840823178, 2775363693, 2711558705, 2649357331, 2588710834, 2529572495, 2471897505, 2415642850, 2360767210, 2307230874, 2254995644, 2204024760, 2154282824, 2105735725, 2058350584, 2012095680, 1966940404, 1922855199, 1879811511, 1837781744, 1796739215, 1756658112, 1717513454, 1679281059, 1641937505, 1605460099, 1569826848, 1535016429, 1501008160, 1467781978, 1435318413, 1403598562, 1372604074, 1342317122, 1312720388, 1283797044, 1255530732, 1227905549, 1200906031, 1174517137, 1148724236, 1123513088, 1098869840, 1074781004, 1051233452, 1028214398, 1005711394, 983712313, 962205344, 941178977, 920621999, 900523482, 880872775, 861659496, 842873523, 824504987, 806544267, 788981978, 771808968, 755016311, 738595300, 722537439, 706834441, 691478218, 676460881, 661774729, 647412246, 633366098, 619629125, 606194338, 593054914, 580204195, 567635675, 555343007, 543319990, 531560571, 520058838, 508809017, 497805469, 487042688, 476515294, 466218034, 456145774, 446293502, 436656319, 427229442, 418008195]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1207).prefactor = (1475424137851191/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1207).cutoff/(generalMeanRows 1207).c)).2 =
    (639369474879489/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1207).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1207).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1207).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1207

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1207).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1207).criticalRate j.val*(generalMeanRows 1207).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1207).c*(generalMeanRows 1207).criticalPoint j.val)).2-
      (generalMeanRows 1207).J/2-(generalMeanRows 1207).error (generalMeanGrid j.val)+
      (generalMeanRows 1207).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1207).c)).2-
      (generalMeanRows 1207).J/2-(generalMeanRows 1207).error 4 := by
  have he : (generalMeanRows 1207).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1207) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1207)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1207

/-! Kernel-checked entropy margins for general spectral rectangle 1208. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1208
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6867479933, 6674694945, 6489262771, 6310765524, 6138817870, 5973063936, 5813174557, 5658844820, 5509791873, 5365752957, 5226483650, 5091756277, 4961358487, 4835091967, 4712771276, 4594222801, 4479283799, 4367801539, 4259632511, 4154641719, 4052702032, 3953693586, 3857503253, 3764024140, 3673155144, 3584800537, 3498869588, 3415276219, 3333938683, 3254779274, 3177724058, 3102702628, 3029647872, 2958495766, 2889185179, 2821657695, 2755857447, 2691730964, 2629227030, 2568296552, 2508892439, 2450969489, 2394484281, 2339395083, 2285661759, 2233245680, 2182109652, 2132217840, 2083535696, 2036029902, 1989668301, 1944419849, 1900254558, 1857143450, 1815058504, 1773972623, 1733859583, 1694694000, 1656451295, 1619107656, 1582640008, 1547025982, 1512243889, 1478272688, 1445091965, 1412681906, 1381023276, 1350097395, 1319886119, 1290371822, 1261537371, 1233366116, 1205841869, 1178948886, 1152671859, 1126995892, 1101906493, 1077389561, 1053431368, 1030018555, 1007138110, 984777367, 962923988, 941565957, 920691567, 900289413, 880348382, 860857644, 841806643, 823185091, 804982958, 787190466, 769798080, 752796504, 736176671, 719929739, 704047084, 688520291, 673341155, 658501668, 643994018, 629810583, 615943924, 602386784, 589132078, 576172892, 563502478, 551114249, 539001776, 527158781, 515579137, 504256860, 493186110, 482361183, 471776510, 461426654, 451306303, 441410271, 431733495, 422271027, 413018037]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1208).prefactor = (3078398818913341/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1208).cutoff/(generalMeanRows 1208).c)).2 =
    (634652485001349/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1208).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1208).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1208).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1208

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1208).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1208).criticalRate j.val*(generalMeanRows 1208).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1208).c*(generalMeanRows 1208).criticalPoint j.val)).2-
      (generalMeanRows 1208).J/2-(generalMeanRows 1208).error (generalMeanGrid j.val)+
      (generalMeanRows 1208).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1208).c)).2-
      (generalMeanRows 1208).J/2-(generalMeanRows 1208).error 4 := by
  have he : (generalMeanRows 1208).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1208) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1208)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1208

/-! Kernel-checked entropy margins for general spectral rectangle 1209. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1209
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5785541924, 5619564718, 5459893319, 5306171824, 5158072384, 5015292479, 4877552503, 4744593613, 4616175813, 4492076238, 4372087622, 4256016921, 4143684078, 4034920915, 3929570125, 3827484375, 3728525485, 3632563692, 3539476980, 3449150473, 3361475885, 3276351019, 3193679310, 3113369409, 3035334807, 2959493485, 2885767602, 2814083200, 2744369946, 2676560881, 2610592203, 2546403061, 2483935361, 2423133601, 2363944703, 2306317871, 2250204453, 2195557812, 2142333216, 2090487723, 2039980087, 1990770661, 1942821313, 1896095345, 1850557417, 1806173482, 1762910716, 1720737461, 1679623166, 1639538338, 1600454487, 1562344084, 1525180515, 1488938045, 1453591770, 1419117592, 1385492176, 1352692925, 1320697944, 1289486015, 1259036570, 1229329662, 1200345945, 1172066650, 1144473561, 1117548997, 1091275793, 1065637278, 1040617259, 1016200005, 992370232, 969113083, 946414117, 924259296, 902634968, 881527858, 860925052, 840813988, 821182444, 802018529, 783310667, 765047595, 747218346, 729812246, 712818901, 696228190, 680030258, 664215506, 648774584, 633698386, 618978039, 604604900, 590570547, 576866773, 563485582, 550419179, 537659970, 525200550, 513033704, 501152395, 489549767, 478219132, 467153973, 456347934, 445794816, 435488576, 425423320, 415593302, 405992915, 396616693, 387459303, 378515544, 369780342, 361248749, 352915937, 344777195, 336827930, 329063657, 321480005, 314072704, 306837592]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1209).prefactor = (5407617040083821/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1209).cutoff/(generalMeanRows 1209).c)).2 =
    (337037449583589/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1209).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1209).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1209).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1209

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1209).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1209).criticalRate j.val*(generalMeanRows 1209).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1209).c*(generalMeanRows 1209).criticalPoint j.val)).2-
      (generalMeanRows 1209).J/2-(generalMeanRows 1209).error (generalMeanGrid j.val)+
      (generalMeanRows 1209).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1209).c)).2-
      (generalMeanRows 1209).J/2-(generalMeanRows 1209).error 4 := by
  have he : (generalMeanRows 1209).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1209) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1209)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1209

/-! Kernel-checked entropy margins for general spectral rectangle 1210. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1210
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6253001415, 6079727550, 5912926434, 5752231896, 5597306816, 5447840300, 5303545165, 5164155710, 5029425720, 4899126691, 4773046230, 4650986637, 4532763612, 4418205111, 4307150298, 4199448617, 4094958939, 3993548798, 3895093698, 3799476485, 3706586774, 3616320434, 3528579111, 3443269801, 3360304460, 3279599643, 3201076176, 3124658862, 3050276203, 2977860150, 2907345873, 2838671552, 2771778177, 2706609375, 2643111243, 2581232195, 2520922825, 2462135773, 2404825611, 2348948727, 2294463229, 2241328840, 2189506822, 2138959882, 2089652105, 2041548878, 1994616825, 1948823748, 1904138564, 1860531256, 1817972821, 1776435221, 1735891343, 1696314954, 1657680664, 1619963887, 1583140810, 1547188358, 1512084165, 1477806544, 1444334461, 1411647508, 1379725879, 1348550349, 1318102247, 1288363443, 1259316320, 1230943762, 1203229132, 1176156259, 1149709415, 1123873310, 1098633066, 1073974212, 1049882667, 1026344727, 1003347051, 980876655, 958920896, 937467462, 916504362, 896019918, 876002753, 856441782, 837326206, 818645499, 800389406, 782547928, 765111321, 748070083, 731414953, 715136899, 699227115, 683677012, 668478215, 653622554, 639102060, 624908960, 611035671, 597474793, 584219108, 571261572, 558595313, 546213622, 534109954, 522277921, 510711288, 499403967, 488350019, 477543645, 466979184, 456651108, 446554023, 436682661, 427031877, 417596651, 408372078, 399353370, 390535850, 381914953, 373486218]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1210).prefactor = (1402326051178223/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1210).cutoff/(generalMeanRows 1210).c)).2 =
    (687805091979083/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1210).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1210).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1210).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1210

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1210).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1210).criticalRate j.val*(generalMeanRows 1210).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1210).c*(generalMeanRows 1210).criticalPoint j.val)).2-
      (generalMeanRows 1210).J/2-(generalMeanRows 1210).error (generalMeanGrid j.val)+
      (generalMeanRows 1210).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1210).c)).2-
      (generalMeanRows 1210).J/2-(generalMeanRows 1210).error 4 := by
  have he : (generalMeanRows 1210).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1210) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1210)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1210

/-! Kernel-checked entropy margins for general spectral rectangle 1211. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1211
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6846176525, 6667623824, 6495561211, 6329619250, 6169458159, 6014764899, 5865250604, 5720648289, 5580710808, 5445209030, 5313930206, 5186676507, 5063263711, 4943520019, 4827284996, 4714408610, 4604750367, 4498178524, 4394569387, 4293806665, 4195780886, 4100388871, 4007533250, 3917122026, 3829068173, 3743289274, 3659707186, 3578247741, 3498840459, 3421418303, 3345917439, 3272277023, 3200439008, 3130347955, 3061950877, 2995197076, 2930038007, 2866427149, 2804319880, 2743673366, 2684446464, 2626599619, 2570094780, 2514895317, 2460965945, 2408272653, 2356782635, 2306464236, 2257286888, 2209221057, 2162238198, 2116310702, 2071411860, 2027515813, 1984597520, 1942632722, 1901597903, 1861470265, 1822227692, 1783848726, 1746312539, 1709598906, 1673688186, 1638561294, 1604199684, 1570585326, 1537700689, 1505528723, 1474052839, 1443256897, 1413125187, 1383642415, 1354793690, 1326564509, 1298940747, 1271908640, 1245454778, 1219566092, 1194229842, 1169433610, 1145165285, 1121413060, 1098165418, 1075411126, 1053139223, 1031339019, 1010000080, 989112223, 968665512, 948650247, 929056959, 909876404, 891099555, 872717599, 854721929, 837104139, 819856020, 802969551, 786436898, 770250408, 754402605, 738886181, 723693998, 708819081, 694254612, 679993927, 666030516, 652358013, 638970196, 625860984, 613024430, 600454724, 588146181, 576093245, 564290484, 552732585, 541414355, 530330713, 519476691, 508847432, 498438184]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1211).prefactor = (286695474079043/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1211).cutoff/(generalMeanRows 1211).c)).2 =
    (355558085423773/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1211).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1211).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1211).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1211

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1211).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1211).criticalRate j.val*(generalMeanRows 1211).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1211).c*(generalMeanRows 1211).criticalPoint j.val)).2-
      (generalMeanRows 1211).J/2-(generalMeanRows 1211).error (generalMeanGrid j.val)+
      (generalMeanRows 1211).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1211).c)).2-
      (generalMeanRows 1211).J/2-(generalMeanRows 1211).error 4 := by
  have he : (generalMeanRows 1211).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1211) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1211)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1211

/-! Kernel-checked entropy margins for general spectral rectangle 1212. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1212
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6140605516, 5962441003, 5791083962, 5626150387, 5467286477, 5314165704, 5166486218, 5023968531, 4886353456, 4753400265, 4624885036, 4500599176, 4380348092, 4263949993, 4151234813, 4042043243, 3936225844, 3833642261, 3734160497, 3637656263, 3544012382, 3453118252, 3364869355, 3279166807, 3195916951, 3115030987, 3036424626, 2960017783, 2885734289, 2813501626, 2743250692, 2674915578, 2608433361, 2543743921, 2480789766, 2419515876, 2359869550, 2301800277, 2245259605, 2190201025, 2136579867, 2084353194, 2033479713, 1983919688, 1935634856, 1888588356, 1842744655, 1798069487, 1754529787, 1712093638, 1670730215, 1630409735, 1591103410, 1552783402, 1515422785, 1478995501, 1443476325, 1408840832, 1375065362, 1342126988, 1310003491, 1278673329, 1248115609, 1218310068, 1189237044, 1160877454, 1133212779, 1106225034, 1079896756, 1054210982, 1029151236, 1004701505, 980846230, 957570287, 934858972, 912697992, 891073445, 869971812, 849379942, 829285042, 809674665, 790536701, 771859362, 753631178, 735840981, 718477903, 701531360, 684991049, 668846935, 653089248, 637708472, 622695338, 608040817, 593736115, 579772663, 566142113, 552836332, 539847393, 527167573, 514789345, 502705375, 490908511, 479391786, 468148407, 457171752, 446455365, 435992955, 425778385, 415805674, 406068988, 396562641, 387281088, 378218919, 369370862, 360731773, 352296636, 344060560, 336018774, 328166622, 320499568, 313013182]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1212).prefactor = (5818513668364729/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1212).cutoff/(generalMeanRows 1212).c)).2 =
    (66953974400179/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1212).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1212).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1212).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1212

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1212).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1212).criticalRate j.val*(generalMeanRows 1212).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1212).c*(generalMeanRows 1212).criticalPoint j.val)).2-
      (generalMeanRows 1212).J/2-(generalMeanRows 1212).error (generalMeanGrid j.val)+
      (generalMeanRows 1212).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1212).c)).2-
      (generalMeanRows 1212).J/2-(generalMeanRows 1212).error 4 := by
  have he : (generalMeanRows 1212).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1212) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1212)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1212

/-! Kernel-checked entropy margins for general spectral rectangle 1213. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1213
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6283177919, 6098829297, 5921564833, 5750985094, 5586721993, 5428435760, 5275812244, 5128560514, 4986410726, 4849112205, 4716431738, 4588152038, 4464070365, 4343997287, 4227755561, 4115179127, 4006112191, 3900408405, 3797930120, 3698547703, 3602138927, 3508588407, 3417787094, 3329631806, 3244024808, 3160873420, 3080089670, 3001589963, 2925294787, 2851128442, 2779018788, 2708897014, 2640697429, 2574357266, 2509816502, 2447017695, 2385905827, 2326428163, 2268534123, 2212175160, 2157304643, 2103877759, 2051851410, 2001184126, 1951835982, 1903768516, 1856944657, 1811328659, 1766886035, 1723583497, 1681388901, 1640271195, 1600200368, 1561147405, 1523084244, 1485983732, 1449819592, 1414566381, 1380199459, 1346694954, 1314029734, 1282181378, 1251128145, 1220848951, 1191323345, 1162531483, 1134454106, 1107072520, 1080368576, 1054324649, 1028923621, 1004148864, 979984220, 956413990, 933422915, 910996163, 889119313, 867778345, 846959625, 826649891, 806836245, 787506140, 768647368, 750248050, 732296627, 714781849, 697692766, 681018721, 664749338, 648874514, 633384415, 618269464, 603520335, 589127944, 575083446, 561378225, 548003888, 534952260, 522215375, 509785474, 497654997, 485816577, 474263035, 462987377, 451982786, 441242618, 430760398, 420529817, 410544722, 400799118, 391287161, 382003153, 372941539, 364096906, 355463973, 347037594, 338812751, 330784550, 322948220, 315299109, 307832681]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1213).prefactor = (6035525989213141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1213).cutoff/(generalMeanRows 1213).c)).2 =
    (665025063647263/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1213).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1213).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1213).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1213

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1213).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1213).criticalRate j.val*(generalMeanRows 1213).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1213).c*(generalMeanRows 1213).criticalPoint j.val)).2-
      (generalMeanRows 1213).J/2-(generalMeanRows 1213).error (generalMeanGrid j.val)+
      (generalMeanRows 1213).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1213).c)).2-
      (generalMeanRows 1213).J/2-(generalMeanRows 1213).error 4 := by
  have he : (generalMeanRows 1213).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1213) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1213)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1213

/-! Kernel-checked entropy margins for general spectral rectangle 1214. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1214
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6790462593, 6597868993, 6412551083, 6234097950, 6062131139, 5896301499, 5736286388, 5581787178, 5432527036, 5288248941, 5148713902, 5013699373, 4882997817, 4756415418, 4633770928, 4514894615, 4399627321, 4287819605, 4179330972, 4074029167, 3971789541, 3872494467, 3776032819, 3682299483, 3591194927, 3502624795, 3416499544, 3332734109, 3251247595, 3171962999, 3094806948, 3019709467, 2946603758, 2875425997, 2806115158, 2738612831, 2672863077, 2608812271, 2546408977, 2485603817, 2426349360, 2368600013, 2312311921, 2257442876, 2203952233, 2151800823, 2100950886, 2051366000, 2003011011, 1955851977, 1909856110, 1864991721, 1821228175, 1778535836, 1736886029, 1696250999, 1656603866, 1617918595, 1580169958, 1543333501, 1507385513, 1472302999, 1438063650, 1404645818, 1372028490, 1340191265, 1309114332, 1278778447, 1249164918, 1220255576, 1192032767, 1164479326, 1137578568, 1111314264, 1085670633, 1060632321, 1036184393, 1012312316, 989001945, 966239515, 944011626, 922305230, 901107628, 880406449, 860189647, 840445489, 821162548, 802329689, 783936065, 765971109, 748424519, 731286261, 714546553, 698195861, 682224891, 666624585, 651386110, 636500856, 621960427, 607756638, 593881504, 580327242, 567086258, 554151149, 541514691, 529169840, 517109724, 505327639, 493817045, 482571563, 471584966, 460851183, 450364286, 440118494, 430108164, 420327789, 410771997, 401435543, 392313310, 383400303, 374691647]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1214).prefactor = (6260632189372349/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1214).cutoff/(generalMeanRows 1214).c)).2 =
    (678630715703041/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1214).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1214).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1214).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1214

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1214).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1214).criticalRate j.val*(generalMeanRows 1214).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1214).c*(generalMeanRows 1214).criticalPoint j.val)).2-
      (generalMeanRows 1214).J/2-(generalMeanRows 1214).error (generalMeanGrid j.val)+
      (generalMeanRows 1214).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1214).c)).2-
      (generalMeanRows 1214).J/2-(generalMeanRows 1214).error 4 := by
  have he : (generalMeanRows 1214).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1214) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1214)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1214

/-! Kernel-checked entropy margins for general spectral rectangle 1215. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1215
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7440729823, 7239394102, 7045496562, 6858615524, 6678362915, 6504380993, 6336339434, 6173932745, 6016877951, 5864912540, 5717792609, 5575291216, 5437196892, 5303312304, 5173453052, 5047446586, 4925131223, 4806355262, 4690976182, 4578859911, 4469880170, 4363917872, 4260860574, 4160601982, 4063041495, 3968083798, 3875638475, 3785619672, 3697945776, 3612539127, 3529325753, 3448235125, 3369199932, 3292155878, 3217041490, 3143797942, 3072368898, 3002700359, 2934740526, 2868439677, 2803750042, 2740625699, 2679022473, 2618897837, 2560210830, 2502921972, 2446993190, 2392387748, 2339070179, 2287006223, 2236162775, 2186507822, 2138010402, 2090640550, 2044369256, 1999168424, 1955010831, 1911870094, 1869720629, 1828537623, 1788297001, 1748975399, 1710550134, 1672999179, 1636301136, 1600435216, 1565381216, 1531119496, 1497630959, 1464897034, 1432899656, 1401621249, 1371044710, 1341153393, 1311931092, 1283362031, 1255430845, 1228122571, 1201422634, 1175316833, 1149791333, 1124832649, 1100427641, 1076563501, 1053227741, 1030408186, 1008092967, 986270507, 964929515, 944058980, 923648161, 903686579, 884164009, 865070476, 846396247, 828131821, 810267929, 792795522, 775705768, 758990046, 742639938, 726647228, 711003894, 695702103, 680734206, 666092733, 651770391, 637760056, 624054771, 610647741, 597532328, 584702049, 572150569, 559871704, 547859407, 536107774, 524611035, 513363553, 502359820, 491594454, 481062196]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1215).prefactor = (6494134145169207/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1215).cutoff/(generalMeanRows 1215).c)).2 =
    (87133052173987/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1215).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1215).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1215).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1215

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1215).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1215).criticalRate j.val*(generalMeanRows 1215).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1215).c*(generalMeanRows 1215).criticalPoint j.val)).2-
      (generalMeanRows 1215).J/2-(generalMeanRows 1215).error (generalMeanGrid j.val)+
      (generalMeanRows 1215).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1215).c)).2-
      (generalMeanRows 1215).J/2-(generalMeanRows 1215).error 4 := by
  have he : (generalMeanRows 1215).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1215) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1215)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1215

/-! Kernel-checked entropy margins for general spectral rectangle 1216. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1216
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7957844782, 7752893334, 7555352069, 7364798502, 7180844134, 7003131123, 6831329326, 6665133675, 6504261833, 6348452097, 6197461533, 6051064292, 5909050104, 5771222928, 5637399728, 5507409374, 5381091650, 5258296355, 5138882493, 5022717534, 4909676746, 4799642591, 4692504169, 4588156721, 4486501165, 4387443685, 4290895345, 4196771744, 4104992694, 4015481933, 3928166852, 3842978254, 3759850127, 3678719438, 3599525939, 3522211999, 3446722432, 3373004359, 3301007060, 3230681857, 3161981985, 3094862493, 3029280137, 2965193290, 2902561850, 2841347166, 2781511955, 2723020238, 2665837273, 2609929494, 2555264451, 2501810762, 2449538060, 2398416948, 2348418953, 2299516489, 2251682813, 2204891994, 2159118877, 2114339049, 2070528811, 2027665152, 1985725715, 1944688777, 1904533225, 1865238530, 1826784728, 1789152398, 1752322643, 1716277073, 1680997784, 1646467345, 1612668780, 1579585552, 1547201550, 1515501077, 1484468831, 1454089899, 1424349739, 1395234174, 1366729375, 1338821856, 1311498460, 1284746352, 1258553005, 1232906197, 1207793997, 1183204761, 1159127119, 1135549974, 1112462487, 1089854075, 1067714402, 1046033374, 1024801129, 1004008034, 983644678, 963701867, 944170616, 925042145, 906307875, 887959420, 869988584, 852387357, 835147907, 818262579, 801723889, 785524520, 769657316, 754115284, 738891581, 723979518, 709372554, 695064290, 681048469, 667318970, 653869807, 640695123, 627789191, 615146407, 602761288]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1216).prefactor = (6573887643755597/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1216).cutoff/(generalMeanRows 1216).c)).2 =
    (715844312043493/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1216).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1216).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1216).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1216

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1216).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1216).criticalRate j.val*(generalMeanRows 1216).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1216).c*(generalMeanRows 1216).criticalPoint j.val)).2-
      (generalMeanRows 1216).J/2-(generalMeanRows 1216).error (generalMeanGrid j.val)+
      (generalMeanRows 1216).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1216).c)).2-
      (generalMeanRows 1216).J/2-(generalMeanRows 1216).error 4 := by
  have he : (generalMeanRows 1216).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1216) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1216)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1216

/-! Kernel-checked entropy margins for general spectral rectangle 1217. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1217
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6113764444, 5941851999, 5776291122, 5616727625, 5462835677, 5314314985, 5170888287, 5032299131, 4898309903, 4768700069, 4643264604, 4521812589, 4404165955, 4290158360, 4179634173, 4072447568, 3968461702, 3867547980, 3769585383, 3674459871, 3582063830, 3492295582, 3405058936, 3320262776, 3237820693, 3157650646, 3079674653, 3003818511, 2930011537, 2858186334, 2788278574, 2720226801, 2653972251, 2589458682, 2526632222, 2465441228, 2405836153, 2347769429, 2291195354, 2236069986, 2182351053, 2129997859, 2078971206, 2029233311, 1980747745, 1933479354, 1887394209, 1842459538, 1798643679, 1755916024, 1714246977, 1673607904, 1633971094, 1595309719, 1557597796, 1520810154, 1484922400, 1449910886, 1415752684, 1382425553, 1349907916, 1318178834, 1287217982, 1257005627, 1227522608, 1198750311, 1170670654, 1143266067, 1116519475, 1090414280, 1064934347, 1040063983, 1015787933, 992091353, 968959808, 946379251, 924336014, 902816798, 881808657, 861298991, 841275532, 821726338, 802639780, 784004534, 765809571, 748044149, 730697805, 713760347, 697221844, 681072622, 665303252, 649904549, 634867560, 620183561, 605844046, 591840728, 578165526, 564810564, 551768162, 539030834, 526591280, 514442382, 502577200, 490988966, 479671080, 468617104, 457820761, 447275928, 436976631, 426917046, 417091489, 407494417, 398120422, 388964228, 380020688, 371284780, 362751604, 354416379, 346274441, 338321237, 330552327]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1217).prefactor = (5647097634721877/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1217).cutoff/(generalMeanRows 1217).c)).2 =
    (147219820267611/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1217).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1217).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1217).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1217

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1217).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1217).criticalRate j.val*(generalMeanRows 1217).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1217).c*(generalMeanRows 1217).criticalPoint j.val)).2-
      (generalMeanRows 1217).J/2-(generalMeanRows 1217).error (generalMeanGrid j.val)+
      (generalMeanRows 1217).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1217).c)).2-
      (generalMeanRows 1217).J/2-(generalMeanRows 1217).error 4 := by
  have he : (generalMeanRows 1217).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1217) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1217)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1217

/-! Kernel-checked entropy margins for general spectral rectangle 1218. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1218
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5907349234, 5759532745, 5616899150, 5479155829, 5346034042, 5217286538, 5092685440, 4972020365, 4855096753, 4741734380, 4631766029, 4525036299, 4421400545, 4320723925, 4222880536, 4127752654, 4035230030, 3945209269, 3857593267, 3772290696, 3689215541, 3608286689, 3529427538, 3452565661, 3377632488, 3304563018, 3233295567, 3163771521, 3095935128, 3029733294, 2965115402, 2902033153, 2840440403, 2780293032, 2721548814, 2664167296, 2608109691, 2553338778, 2499818812, 2447515433, 2396395594, 2346427481, 2297580451, 2249824968, 2203132542, 2157475677, 2112827821, 2069163319, 2026457369, 1984685978, 1943825931, 1903854749, 1864750657, 1826492555, 1789059987, 1752433111, 1716592680, 1681520008, 1647196956, 1613605905, 1580729736, 1548551813, 1517055962, 1486226457, 1456047998, 1426505702, 1397585085, 1369272046, 1341552858, 1314414150, 1287842902, 1261826427, 1236352362, 1211408659, 1186983572, 1163065653, 1139643734, 1116706928, 1094244612, 1072246424, 1050702255, 1029602240, 1008936749, 988696386, 968871977, 949454565, 930435405, 911805958, 893557883, 875683036, 858173458, 841021378, 824219202, 807759509, 791635049, 775838738, 760363651, 745203019, 730350229, 715798813, 701542450, 687574959, 673890299, 660482559, 647345964, 634474864, 621863732, 609507166, 597399880, 585536705, 573912583, 562522570, 551361824, 540425614, 529709306, 519208370, 508918371, 498834972, 488953927, 479271082, 469782372]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1218).prefactor = (2378123518475113/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1218).cutoff/(generalMeanRows 1218).c)).2 =
    (766954052386103/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1218).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1218).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1218).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1218

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1218).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1218).criticalRate j.val*(generalMeanRows 1218).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1218).c*(generalMeanRows 1218).criticalPoint j.val)).2-
      (generalMeanRows 1218).J/2-(generalMeanRows 1218).error (generalMeanGrid j.val)+
      (generalMeanRows 1218).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1218).c)).2-
      (generalMeanRows 1218).J/2-(generalMeanRows 1218).error 4 := by
  have he : (generalMeanRows 1218).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1218) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1218)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1218

/-! Kernel-checked entropy margins for general spectral rectangle 1219. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1219
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6052642858, 5899266921, 5751298079, 5608431588, 5470387506, 5336908223, 5207756257, 5082712308, 4961573520, 4844151943, 4730273146, 4619774988, 4512506514, 4408326963, 4307104879, 4208717311, 4113049092, 4019992190, 3929445121, 3841312416, 3755504144, 3671935478, 3590526293, 3511200817, 3433887298, 3358517709, 3285027480, 3213355247, 3143442631, 3075234029, 3008676429, 2943719232, 2880314100, 2818414803, 2757977096, 2698958585, 2641318621, 2585018196, 2530019840, 2476287539, 2423786653, 2372483832, 2322346955, 2273345059, 2225448280, 2178627795, 2132855773, 2088105321, 2044350442, 2001565991, 1959727638, 1918811824, 1878795733, 1839657255, 1801374958, 1763928057, 1727296387, 1691460381, 1656401039, 1622099912, 1588539077, 1555701117, 1523569104, 1492126577, 1461357527, 1431246383, 1401777991, 1372937604, 1344710866, 1317083798, 1290042788, 1263574575, 1237666240, 1212305194, 1187479170, 1163176208, 1139384648, 1116093123, 1093290545, 1070966102, 1049109246, 1027709685, 1006757378, 986242528, 966155569, 946487169, 927228214, 908369810, 889903269, 871820110, 854112051, 836771002, 819789060, 803158508, 786871805, 770921584, 755300648, 740001964, 725018657, 710344012, 695971464, 681894597, 668107139, 654602958, 641376062, 628420592, 615730818, 603301139, 591126079, 579200281, 567518508, 556075638, 544866663, 533886683, 523130905, 512594644, 502273314, 492162431, 482257607, 472554550, 463049062]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1219).prefactor = (987987857652987/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1219).cutoff/(generalMeanRows 1219).c)).2 =
    (762292039280291/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1219).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1219).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1219).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1219

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1219).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1219).criticalRate j.val*(generalMeanRows 1219).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1219).c*(generalMeanRows 1219).criticalPoint j.val)).2-
      (generalMeanRows 1219).J/2-(generalMeanRows 1219).error (generalMeanGrid j.val)+
      (generalMeanRows 1219).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1219).c)).2-
      (generalMeanRows 1219).J/2-(generalMeanRows 1219).error 4 := by
  have he : (generalMeanRows 1219).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1219) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1219)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1219

/-! Kernel-checked entropy margins for general spectral rectangle 1220. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1220
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6201561256, 6042440508, 5888960240, 5740803063, 5597677364, 5459314726, 5325467652, 5195907539, 5070422879, 4948817657, 4830909918, 4716530483, 4605521812, 4497736965, 4393038686, 4291298571, 4192396315, 4096219042, 4002660694, 3911621480, 3823007377, 3736729677, 3652704579, 3570852814, 3491099308, 3413372872, 3337605923, 3263734225, 3191696656, 3121434994, 3052893722, 2986019845, 2920762729, 2857073947, 2794907143, 2734217900, 2674963627, 2617103447, 2560598095, 2505409834, 2451502356, 2398840717, 2347391252, 2297121512, 2248000201, 2199997115, 2153083089, 2107229943, 2062410438, 2018598228, 1975767822, 1933894541, 1892954484, 1852924494, 1813782123, 1775505605, 1738073828, 1701466301, 1665663138, 1630645026, 1596393209, 1562889460, 1530116067, 1498055810, 1466691947, 1436008191, 1405988698, 1376618051, 1347881243, 1319763666, 1292251096, 1265329681, 1238985925, 1213206685, 1187979148, 1163290833, 1139129571, 1115483499, 1092341051, 1069690950, 1047522195, 1025824058, 1004586072, 983798027, 963449959, 943532144, 924035095, 904949548, 886266462, 867977012, 850072578, 832544748, 815385304, 798586221, 782139663, 766037974, 750273677, 734839467, 719728207, 704932925, 690446809, 676263200, 662375593, 648777631, 635463101, 622425929, 609660178, 597160048, 584919865, 572934085, 561197287, 549704170, 538449553, 527428369, 516635663, 506066590, 495716413, 485580499, 475654316, 465933432, 456413515]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1220).prefactor = (5130725965695637/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1220).cutoff/(generalMeanRows 1220).c)).2 =
    (75765165972379/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1220).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1220).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1220).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1220

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1220).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1220).criticalRate j.val*(generalMeanRows 1220).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1220).c*(generalMeanRows 1220).criticalPoint j.val)).2-
      (generalMeanRows 1220).J/2-(generalMeanRows 1220).error (generalMeanGrid j.val)+
      (generalMeanRows 1220).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1220).c)).2-
      (generalMeanRows 1220).J/2-(generalMeanRows 1220).error 4 := by
  have he : (generalMeanRows 1220).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1220) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1220)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1220

/-! Kernel-checked entropy margins for general spectral rectangle 1221. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1221
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6441073363, 6275807171, 6116399301, 5962520108, 5813866714, 5670160337, 5531143920, 5396580032, 5266248997, 5139947229, 5017485743, 4898688831, 4783392865, 4671445231, 4562703374, 4457033927, 4354311941, 4254420180, 4157248491, 4062693228, 3970656737, 3881046884, 3793776630, 3708763647, 3625929960, 3545201632, 3466508468, 3389783751, 3314964001, 3241988745, 3170800323, 3101343692, 3033566264, 2967417742, 2902849977, 2839816839, 2778274092, 2718179278, 2659491619, 2602171917, 2546182465, 2491486967, 2438050458, 2385839238, 2334820800, 2284963775, 2236237869, 2188613817, 2142063326, 2096559034, 2052074464, 2008583984, 1966062770, 1924486771, 1883832673, 1844077868, 1805200428, 1767179073, 1729993146, 1693622591, 1658047925, 1623250219, 1589211076, 1555912613, 1523337438, 1491468636, 1460289752, 1429784774, 1399938114, 1370734601, 1342159461, 1314198307, 1286837122, 1260062255, 1233860399, 1208218590, 1183124190, 1158564876, 1134528638, 1111003761, 1087978821, 1065442675, 1043384452, 1021793546, 1000659610, 979972544, 959722494, 939899839, 920495189, 901499377, 882903452, 864698675, 846876511, 829428627, 812346882, 795623326, 779250192, 763219893, 747525017, 732158323, 717112734, 702381336, 687957373, 673834241, 660005486, 646464802, 633206022, 620223121, 607510207, 595061521, 582871433, 570934438, 559245153, 547798317, 536588783, 525611519, 514861605, 504334229, 494024684, 483928368, 474040779]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1221).prefactor = (5328881064914743/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1221).cutoff/(generalMeanRows 1221).c)).2 =
    (75765165972379/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1221).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1221).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1221).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1221

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1221).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1221).criticalRate j.val*(generalMeanRows 1221).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1221).c*(generalMeanRows 1221).criticalPoint j.val)).2-
      (generalMeanRows 1221).J/2-(generalMeanRows 1221).error (generalMeanGrid j.val)+
      (generalMeanRows 1221).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1221).c)).2-
      (generalMeanRows 1221).J/2-(generalMeanRows 1221).error 4 := by
  have he : (generalMeanRows 1221).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1221) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1221)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1221

/-! Kernel-checked entropy margins for general spectral rectangle 1222. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1222
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5319217026, 5173925951, 5033826387, 4898634091, 4768087782, 4641946803, 4519989052, 4402009155, 4287816847, 4177235531, 4070100997, 3966260281, 3865570650, 3767898683, 3673119463, 3581115841, 3491777781, 3405001768, 3320690274, 3238751283, 3159097852, 3081647722, 3006322962, 2933049646, 2861757563, 2792379950, 2724853248, 2659116885, 2595113074, 2532786626, 2472084784, 2412957070, 2355355140, 2299232657, 2244545171, 2191250006, 2139306161, 2088674217, 2039316248, 1991195740, 1944277520, 1898527684, 1853913532, 1810403513, 1767967162, 1726575055, 1686198755, 1646810770, 1608384510, 1570894245, 1534315068, 1498622863, 1463794268, 1429806647, 1396638055, 1364267219, 1332673504, 1301836892, 1271737956, 1242357842, 1213678243, 1185681382, 1158349991, 1131667294, 1105616992, 1080183239, 1055350637, 1031104211, 1007429402, 984312048, 961738374, 939694979, 918168824, 897147220, 876617816, 856568591, 836987842, 817864173, 799186490, 780943987, 763126140, 745722699, 728723677, 712119346, 695900228, 680057086, 664580919, 649462955, 634694646, 620267657, 606173866, 592405352, 578954396, 565813469, 552975231, 540432524, 528178369, 516205958, 504508653, 493079978, 481913616, 471003407, 460343340, 449927551, 439750321, 429806067, 420089346, 410594843, 401317373, 392251878, 383393420, 374737181, 366278459, 358012664, 349935317, 342042047, 334328586, 326790769, 319424530, 312225900, 305191003]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1222).prefactor = (595136863151553/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1222).cutoff/(generalMeanRows 1222).c)).2 =
    (397495713458091/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1222).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1222).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1222).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1222

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1222).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1222).criticalRate j.val*(generalMeanRows 1222).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1222).c*(generalMeanRows 1222).criticalPoint j.val)).2-
      (generalMeanRows 1222).J/2-(generalMeanRows 1222).error (generalMeanGrid j.val)+
      (generalMeanRows 1222).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1222).c)).2-
      (generalMeanRows 1222).J/2-(generalMeanRows 1222).error 4 := by
  have he : (generalMeanRows 1222).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1222) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1222)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1222

/-! Kernel-checked entropy margins for general spectral rectangle 1223. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1223
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6068129824, 5893146287, 5724730421, 5562516164, 5406166483, 5255370508, 5109840991, 4969312054, 4833537181, 4702287428, 4575349826, 4452525952, 4333630645, 4218490859, 4106944625, 3998840126, 3894034851, 3792394843, 3693794012, 3598113513, 3505241188, 3415071056, 3327502846, 3242441579, 3159797187, 3079484155, 3001421212, 2925531031, 2851739968, 2779977815, 2710177573, 2642275254, 2576209685, 2511922337, 2449357165, 2388460458, 2329180706, 2271468473, 2215276278, 2160558489, 2107271224, 2055372256, 2004820927, 1955578068, 1907605925, 1860868088, 1815329425, 1770956023, 1727715131, 1685575104, 1644505356, 1604476313, 1565459364, 1527426828, 1490351907, 1454208653, 1418971932, 1384617392, 1351121433, 1318461175, 1286614430, 1255559682, 1225276051, 1195743280, 1166941706, 1138852239, 1111456347, 1084736027, 1058673796, 1033252667, 1008456135, 984268159, 960673149, 937655947, 915201819, 893296435, 871925860, 851076540, 830735290, 810889284, 791526042, 772633419, 754199597, 736213075, 718662655, 701537439, 684826817, 668520460, 652608307, 637080565, 621927694, 607140406, 592709652, 578626619, 564882722, 551469598, 538379098, 525603284, 513134422, 500964974, 489087596, 477495131, 466180605, 455137219, 444358348, 433837535, 423568483, 413545058, 403761279, 394211313, 384889477, 375790228, 366908163, 358238013, 349774642, 341513040, 333448324, 325575730, 317890613, 310388446, 303064809]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1223).prefactor = (2874222915195057/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1223).cutoff/(generalMeanRows 1223).c)).2 =
    (712395068135669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1223).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1223).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1223).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1223

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1223).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1223).criticalRate j.val*(generalMeanRows 1223).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1223).c*(generalMeanRows 1223).criticalPoint j.val)).2-
      (generalMeanRows 1223).J/2-(generalMeanRows 1223).error (generalMeanGrid j.val)+
      (generalMeanRows 1223).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1223).c)).2-
      (generalMeanRows 1223).J/2-(generalMeanRows 1223).error 4 := by
  have he : (generalMeanRows 1223).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1223) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1223)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1223

/-! Kernel-checked entropy margins for general spectral rectangle 1224. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1224
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6732520769, 6551216979, 6376485808, 6207959343, 6045299255, 5888193858, 5736355504, 5589518269, 5447435897, 5309879961, 5176638230, 5047513204, 4922320796, 4800889164, 4683057646, 4568675812, 4457602604, 4349705565, 4244860138, 4142949035, 4043861664, 3947493610, 3853746164, 3762525895, 3673744258, 3587317244, 3503165052, 3421211794, 3341385228, 3263616509, 3187839961, 3113992872, 3042015305, 2971849918, 2903441809, 2836738363, 2771689118, 2708245638, 2646361397, 2585991671, 2527093439, 2469625288, 2413547332, 2358821127, 2305409600, 2253276980, 2202388731, 2152711497, 2104213040, 2056862193, 2010628808, 1965483709, 1921398652, 1878346283, 1836300101, 1795234418, 1755124332, 1715945690, 1677675059, 1640289700, 1603767538, 1568087140, 1533227688, 1499168956, 1465891293, 1433375595, 1401603293, 1370556330, 1340217142, 1310568647, 1281594223, 1253277695, 1225603321, 1198555776, 1172120140, 1146281885, 1121026863, 1096341292, 1072211749, 1048625153, 1025568760, 1003030152, 980997222, 959458174, 938401506, 917816004, 897690737, 878015042, 858778524, 839971043, 821582709, 803603875, 786025129, 768837291, 752031402, 735598721, 719530719, 703819071, 688455655, 673432542, 658741993, 644376454, 630328551, 616591085, 603157029, 590019521, 577171862, 564607508, 552320074, 540303321, 528551158, 517057635, 505816943, 494823406, 484071483, 473555759, 463270946, 453211879, 443373510, 433750911, 424339266]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1224).prefactor = (1470160590083471/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1224).cutoff/(generalMeanRows 1224).c)).2 =
    (92412815131949/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1224).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1224).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1224).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1224

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1224).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1224).criticalRate j.val*(generalMeanRows 1224).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1224).c*(generalMeanRows 1224).criticalPoint j.val)).2-
      (generalMeanRows 1224).J/2-(generalMeanRows 1224).error (generalMeanGrid j.val)+
      (generalMeanRows 1224).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1224).c)).2-
      (generalMeanRows 1224).J/2-(generalMeanRows 1224).error 4 := by
  have he : (generalMeanRows 1224).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1224) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1224)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1224

/-! Kernel-checked entropy margins for general spectral rectangle 1225. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1225
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5758153396, 5602653493, 5452676791, 5307920661, 5168106985, 5032979650, 4902302348, 4775856615, 4653440105, 4534865047, 4419956881, 4308553037, 4200501846, 4095661568, 3993899519, 3895091292, 3799120055, 3705875917, 3615255364, 3527160744, 3441499804, 3358185272, 3277134480, 3198269017, 3121514421, 3046799892, 2974058037, 2903224632, 2834238409, 2767040860, 2701576060, 2637790495, 2575632922, 2515054220, 2456007270, 2398446836, 2342329455, 2287613338, 2234258280, 2182225570, 2131477916, 2081979371, 2033695261, 1986592127, 1940637660, 1895800653, 1852050941, 1809359358, 1767697694, 1727038645, 1687355781, 1648623504, 1610817015, 1573912281, 1537886003, 1502715585, 1468379111, 1434855315, 1402123555, 1370163794, 1338956574, 1308482996, 1278724700, 1249663845, 1221283092, 1193565584, 1166494934, 1140055205, 1114230897, 1089006931, 1064368637, 1040301739, 1016792345, 993826932, 971392334, 949475735, 928064653, 907146935, 886710743, 866744544, 847237107, 828177485, 809555015, 791359305, 773580227, 756207910, 739232733, 722645315, 706436514, 690597414, 675119322, 659993762, 645212468, 630767378, 616650630, 602854554, 589371670, 576194681, 563316467, 550730083, 538428752, 526405862, 514654961, 503169754, 491944096, 480971991, 470247588, 459765175, 449519177, 439504154, 429714792, 420145908, 410792440, 401649446, 392712103, 383975700, 375435638, 367087429, 358926687, 350949132, 343150583]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1225).prefactor = (1017111479873937/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1225).cutoff/(generalMeanRows 1225).c)).2 =
    (799406445125299/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1225).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1225).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1225).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1225

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1225).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1225).criticalRate j.val*(generalMeanRows 1225).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1225).c*(generalMeanRows 1225).criticalPoint j.val)).2-
      (generalMeanRows 1225).J/2-(generalMeanRows 1225).error (generalMeanGrid j.val)+
      (generalMeanRows 1225).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1225).c)).2-
      (generalMeanRows 1225).J/2-(generalMeanRows 1225).error 4 := by
  have he : (generalMeanRows 1225).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1225) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1225)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1225

/-! Kernel-checked entropy margins for general spectral rectangle 1226. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1226
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5951125256, 5790414115, 5635411274, 5485803960, 5341304736, 5201648905, 5066592241, 4935908957, 4809389926, 4686841086, 4568082025, 4452944726, 4341272437, 4232918667, 4127746286, 4025626719, 3926439217, 3830070207, 3736412705, 3645365787, 3556834108, 3470727473, 3386960442, 3305451976, 3226125119, 3148906697, 3073727058, 3000519827, 2929221682, 2859772155, 2792113446, 2726190248, 2661949600, 2599340736, 2538314958, 2478825512, 2420827481, 2364277673, 2309134537, 2255358065, 2202909716, 2151752335, 2101850089, 2053168397, 2005673868, 1959334247, 1914118359, 1869996062, 1826938198, 1784916551, 1743903803, 1703873498, 1664800008, 1626658493, 1589424873, 1553075796, 1517588611, 1482941338, 1449112645, 1416081823, 1383828762, 1352333929, 1321578349, 1291543583, 1262211711, 1233565312, 1205587449, 1178261651, 1151571897, 1125502606, 1100038613, 1075165167, 1050867907, 1027132858, 1003946414, 981295328, 959166701, 937547972, 916426905, 895791583, 875630397, 855932034, 836685473, 817879973, 799505069, 781550557, 764006494, 746863185, 730111182, 713741269, 697744463, 682112003, 666835346, 651906161, 637316321, 623057900, 609123167, 595504580, 582194781, 569186592, 556473009, 544047198, 531902492, 520032383, 508430522, 497090711, 486006903, 475173195, 464583825, 454233170, 444115739, 434226175, 424559246, 415109845, 405872986, 396843802, 388017539, 379389557, 370955326, 362710421, 354650521]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1226).prefactor = (1051197736455863/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1226).cutoff/(generalMeanRows 1226).c)).2 =
    (799406445125299/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1226).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1226).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1226).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1226

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1226).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1226).criticalRate j.val*(generalMeanRows 1226).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1226).c*(generalMeanRows 1226).criticalPoint j.val)).2-
      (generalMeanRows 1226).J/2-(generalMeanRows 1226).error (generalMeanGrid j.val)+
      (generalMeanRows 1226).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1226).c)).2-
      (generalMeanRows 1226).J/2-(generalMeanRows 1226).error 4 := by
  have he : (generalMeanRows 1226).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1226) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1226)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1226

/-! Kernel-checked entropy margins for general spectral rectangle 1227. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1227
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6798709543, 6602658655, 6413966160, 6232221924, 6057048337, 5888097101, 5725046384, 5567598299, 5415476648, 5268424925, 5126204519, 4988593118, 4855383269, 4726381091, 4601405116, 4480285246, 4362861816, 4248984738, 4138512742, 4031312675, 3927258877, 3826232604, 3728121515, 3632819196, 3540224733, 3450242318, 3362780894, 3277753825, 3195078599, 3114676555, 3036472631, 2960395131, 2886375519, 2814348219, 2744250438, 2676022000, 2609605192, 2544944626, 2481987104, 2420681502, 2360978653, 2302831247, 2246193731, 2191022219, 2137274413, 2084909518, 2033888174, 1984172383, 1935725452, 1888511926, 1842497537, 1797649149, 1753934709, 1711323201, 1669784600, 1629289836, 1589810748, 1551320052, 1513791307, 1477198878, 1441517907, 1406724285, 1372794621, 1339706217, 1307437042, 1275965711, 1245271458, 1215334113, 1186134089, 1157652353, 1129870412, 1102770296, 1076334537, 1050546152, 1025388632, 1000845923, 976902412, 953542913, 930752655, 908517265, 886822763, 865655540, 845002356, 824850325, 805186901, 785999875, 767277358, 749007777, 731179861, 713782638, 696805420, 680237798, 664069637, 648291060, 632892450, 617864437, 603197890, 588883917, 574913851, 561279248, 547971880, 534983727, 522306974, 509934007, 497857401, 486069921, 474564515, 463334308, 452372599, 441672854, 431228704, 421033940, 411082509, 401368506, 391886177, 382629910, 373594232, 364773807, 356163432, 347758032, 339552658]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1227).prefactor = (257621472562503/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1227).cutoff/(generalMeanRows 1227).c)).2 =
    (712395068135669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1227).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1227).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1227).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1227

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1227).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1227).criticalRate j.val*(generalMeanRows 1227).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1227).c*(generalMeanRows 1227).criticalPoint j.val)).2-
      (generalMeanRows 1227).J/2-(generalMeanRows 1227).error (generalMeanGrid j.val)+
      (generalMeanRows 1227).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1227).c)).2-
      (generalMeanRows 1227).J/2-(generalMeanRows 1227).error 4 := by
  have he : (generalMeanRows 1227).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1227) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1227)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1227

/-! Kernel-checked entropy margins for general spectral rectangle 1228. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1228
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7353468886, 7148431757, 6950956855, 6760621993, 6577038694, 6399848850, 6228721764, 6063351520, 5903454651, 5748768048, 5599047103, 5454064045, 5313606447, 5177475886, 5045486745, 4917465122, 4793247866, 4672681684, 4555622354, 4441934002, 4331488448, 4224164618, 4119848005, 4018430179, 3919808344, 3823884933, 3730567239, 3639767076, 3551400469, 3465387375, 3381651422, 3300119673, 3220722402, 3143392904, 3068067301, 2994684374, 2923185411, 2853514055, 2785616175, 2719439740, 2654934703, 2592052899, 2530747939, 2470975125, 2412691359, 2355855065, 2300426117, 2246365765, 2193636574, 2142202360, 2092028136, 2043080056, 1995325367, 1948732360, 1903270328, 1858909519, 1815621104, 1773377136, 1732150513, 1691914947, 1652644936, 1614315725, 1576903289, 1540384298, 1504736094, 1469936667, 1435964635, 1402799216, 1370420211, 1338807985, 1307943444, 1277808021, 1248383656, 1219652781, 1191598303, 1164203588, 1137452450, 1111329133, 1085818298, 1060905014, 1036574740, 1012813317, 989606957, 966942228, 944806046, 923185667, 902068672, 881442960, 861296743, 841618528, 822397116, 803621593, 785281318, 767365918, 749865282, 732769550, 716069109, 699754587, 683816842, 668246961, 653036250, 638176230, 623658631, 609475386, 595618625, 582080674, 568854042, 555931424, 543305690, 530969887, 518917228, 507141091, 495635014, 484392691, 473407969, 462674842, 452187448, 441940068, 431927117, 422143147, 412582838]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1228).prefactor = (267571138320899/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1228).cutoff/(generalMeanRows 1228).c)).2 =
    (725758295947837/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1228).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1228).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1228).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1228

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1228).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1228).criticalRate j.val*(generalMeanRows 1228).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1228).c*(generalMeanRows 1228).criticalPoint j.val)).2-
      (generalMeanRows 1228).J/2-(generalMeanRows 1228).error (generalMeanGrid j.val)+
      (generalMeanRows 1228).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1228).c)).2-
      (generalMeanRows 1228).J/2-(generalMeanRows 1228).error 4 := by
  have he : (generalMeanRows 1228).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1228) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1228)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1228

/-! Kernel-checked entropy margins for general spectral rectangle 1229. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1229
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8077734657, 7867907223, 7665559018, 7470269816, 7281653430, 7099354315, 6923044562, 6752421227, 6587203958, 6427132876, 6271966685, 6121480989, 5975466771, 5833729040, 5696085612, 5562366014, 5432410490, 5306069120, 5183201006, 5063673549, 4947361790, 4834147812, 4723920197, 4616573537, 4512007983, 4410128839, 4310846191, 4214074565, 4119732621, 4027742870, 3938031410, 3850527692, 3765164305, 3681876768, 3600603353, 3521284914, 3443864727, 3368288354, 3294503502, 3222459906, 3152109212, 3083404874, 3016302057, 2950757542, 2886729648, 2824178150, 2763064207, 2703350293, 2645000138, 2587978662, 2532251924, 2477787072, 2424552288, 2372516750, 2321650581, 2271924818, 2223311366, 2175782966, 2129313162, 2083876269, 2039447340, 1996002142, 1953517125, 1911969399, 1871336712, 1831597422, 1792730477, 1754715398, 1717532253, 1681161644, 1645584687, 1610782992, 1576738652, 1543434222, 1510852710, 1478977557, 1447792628, 1417282196, 1387430929, 1358223881, 1329646480, 1301684512, 1274324117, 1247551774, 1221354296, 1195718814, 1170632773, 1146083921, 1122060300, 1098550242, 1075542355, 1053025518, 1030988876, 1009421829, 988314028, 967655367, 947435976, 927646216, 908276673, 889318151, 870761667, 852598445, 834819913, 817417695, 800383606, 783709650, 767388012, 751411057, 735771320, 720461508, 705474494, 690803308, 676441141, 662381334, 648617381, 635142918, 621951726, 609037725, 596394968, 584017643, 571900066]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1229).prefactor = (1693577282948463/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1229).cutoff/(generalMeanRows 1229).c)).2 =
    (150606542773499/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1229).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1229).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1229).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1229

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1229).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1229).criticalRate j.val*(generalMeanRows 1229).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1229).c*(generalMeanRows 1229).criticalPoint j.val)).2-
      (generalMeanRows 1229).J/2-(generalMeanRows 1229).error (generalMeanGrid j.val)+
      (generalMeanRows 1229).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1229).c)).2-
      (generalMeanRows 1229).J/2-(generalMeanRows 1229).error 4 := by
  have he : (generalMeanRows 1229).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1229) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1229)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1229

/-! Kernel-checked entropy margins for general spectral rectangle 1230. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1230
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5983856256, 5809310271, 5641231412, 5479266346, 5323089872, 5172402076, 5026925822, 4886404525, 4750600184, 4619291628, 4492272954, 4369352142, 4250349811, 4135098103, 4023439696, 3915226903, 3810320873, 3708590866, 3609913605, 3514172683, 3421258034, 3331065454, 3243496160, 3158456398, 3075857081, 2995613462, 2917644837, 2841874270, 2768228346, 2696636943, 2627033021, 2559352434, 2493533752, 2429518099, 2367249004, 2306672265, 2247735819, 2190389627, 2134585563, 2080277315, 2027420291, 1975971529, 1925889619, 1877134628, 1829668026, 1783452620, 1738452496, 1694632960, 1651960479, 1610402636, 1569928080, 1530506479, 1492108481, 1454705669, 1418270529, 1382776410, 1348197490, 1314508747, 1281685926, 1249705510, 1218544695, 1188181361, 1158594049, 1129761935, 1101664813, 1074283065, 1047597648, 1021590071, 996242377, 971537124, 947457368, 923986649, 901108972, 878808794, 857071008, 835880929, 815224284, 795087194, 775456164, 756318074, 737660161, 719470015, 701735562, 684445059, 667587081, 651150513, 635124538, 619498635, 604262560, 589406347, 574920296, 560794964, 547021163, 533589945, 520492600, 507720650, 495265840, 483120132, 471275699, 459724919, 448460372, 437474830, 426761254, 416312789, 406122757, 396184655, 386492148, 377039065, 367819395, 358827282, 350057022, 341503055, 333159968, 325022484, 317085463, 309343896, 301792902, 294427726, 287243734, 280236410, 273401352]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1230).prefactor = (4533065919289/781250000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1230).cutoff/(generalMeanRows 1230).c)).2 =
    (192225747707971/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1230).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1230).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1230).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1230

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1230).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1230).criticalRate j.val*(generalMeanRows 1230).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1230).c*(generalMeanRows 1230).criticalPoint j.val)).2-
      (generalMeanRows 1230).J/2-(generalMeanRows 1230).error (generalMeanGrid j.val)+
      (generalMeanRows 1230).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1230).c)).2-
      (generalMeanRows 1230).J/2-(generalMeanRows 1230).error 4 := by
  have he : (generalMeanRows 1230).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1230) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1230)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1230

/-! Kernel-checked entropy margins for general spectral rectangle 1231. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1231
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6207074247, 6050568003, 5899453327, 5753432135, 5612230767, 5475597497, 5343300327, 5215125035, 5090873450, 4970361912, 4853419907, 4739888845, 4629620970, 4522478391, 4418332205, 4317061718, 4218553737, 4122701945, 4029406326, 3938572653, 3850112026, 3763940450, 3679978457, 3598150762, 3518385952, 3440616197, 3364776999, 3290806951, 3218647529, 3148242888, 3079539690, 3012486936, 2947035819, 2883139585, 2820753404, 2759834259, 2700340832, 2642233414, 2585473803, 2530025230, 2475852276, 2422920798, 2371197866, 2320651699, 2271251607, 2222967937, 2175772024, 2129636143, 2084533464, 2040438016, 1997324641, 1955168965, 1913947361, 1873636918, 1834215410, 1795661271, 1757953563, 1721071959, 1684996712, 1649708635, 1615189083, 1581419929, 1548383546, 1516062790, 1484440984, 1453501897, 1423229734, 1393609118, 1364625077, 1336263029, 1308508774, 1281348474, 1254768648, 1228756159, 1203298201, 1178382291, 1153996258, 1130128235, 1106766649, 1083900210, 1061517909, 1039609001, 1018163006, 997169694, 976619085, 956501435, 936807235, 917527201, 898652270, 880173592, 862082526, 844370633, 827029671, 810051592, 793428532, 777152810, 761216922, 745613539, 730335496, 715375794, 700727595, 686384215, 672339121, 658585929, 645118399, 631930432, 619016064, 606369468, 593984944, 581856923, 569979955, 558348717, 546957999, 535802710, 524877870, 514178609, 503700163, 493437876, 483387191, 473543653, 463902902]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1231).prefactor = (2526622990335011/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1231).cutoff/(generalMeanRows 1231).c)).2 =
    (81171509862407/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1231).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1231).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1231).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1231

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1231).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1231).criticalRate j.val*(generalMeanRows 1231).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1231).c*(generalMeanRows 1231).criticalPoint j.val)).2-
      (generalMeanRows 1231).J/2-(generalMeanRows 1231).error (generalMeanGrid j.val)+
      (generalMeanRows 1231).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1231).c)).2-
      (generalMeanRows 1231).J/2-(generalMeanRows 1231).error 4 := by
  have he : (generalMeanRows 1231).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1231) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1231)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1231

/-! Kernel-checked entropy margins for general spectral rectangle 1232. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1232
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6285296877, 6122926490, 5966214195, 5814848058, 5668541574, 5527031072, 5390073433, 5257444057, 5128935073, 5004353739, 4883521021, 4766270325, 4652446367, 4541904160, 4434508106, 4330131184, 4228654218, 4129965219, 4033958792, 3940535604, 3849601900, 3761069066, 3674853233, 3590874920, 3509058709, 3429332948, 3351629482, 3275883409, 3202032855, 3130018770, 3059784740, 2991276819, 2924443370, 2859234921, 2795604031, 2733505174, 2672894621, 2613730337, 2555971891, 2499580359, 2444518251, 2390749428, 2338239038, 2286953443, 2236860166, 2187927830, 2140126106, 2093425662, 2047798120, 2003216011, 1959652736, 1917082525, 1875480405, 1834822163, 1795084317, 1756244088, 1718279366, 1681168688, 1644891213, 1609426698, 1574755472, 1540858422, 1507716964, 1475313032, 1443629055, 1412647939, 1382353057, 1352728224, 1323757689, 1295426118, 1267718581, 1240620539, 1214117829, 1188196656, 1162843580, 1138045503, 1113789663, 1090063617, 1066855240, 1044152706, 1021944488, 1000219344, 978966308, 958174688, 937834051, 917934220, 898465266, 879417500, 860781468, 842547943, 824707919, 807252606, 790173423, 773461995, 757110142, 741109880, 725453412, 710133124, 695141582, 680471522, 666115854, 652067650, 638320142, 624866722, 611700931, 598816462, 586207149, 573866972, 561790045, 549970618, 538403074, 527081920, 516001791, 505157442, 494543747, 484155697, 473988393, 464037050, 454296989, 444763635, 435432518]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1232).prefactor = (5255798994837049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1232).cutoff/(generalMeanRows 1232).c)).2 =
    (100333157888019/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1232).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1232).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1232).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1232

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1232).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1232).criticalRate j.val*(generalMeanRows 1232).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1232).c*(generalMeanRows 1232).criticalPoint j.val)).2-
      (generalMeanRows 1232).J/2-(generalMeanRows 1232).error (generalMeanGrid j.val)+
      (generalMeanRows 1232).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1232).c)).2-
      (generalMeanRows 1232).J/2-(generalMeanRows 1232).error 4 := by
  have he : (generalMeanRows 1232).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1232) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1232)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1232

/-! Kernel-checked entropy margins for general spectral rectangle 1233. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1233
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6537235103, 6368356303, 6205362392, 6047928934, 5895757938, 5748575166, 5606127752, 5468182094, 5334521990, 5204946969, 5079270823, 4957320280, 4838933832, 4723960680, 4612259790, 4503699051, 4398154508, 4295509684, 4195654960, 4098487021, 4003908354, 3911826792, 3822155106, 3734810628, 3649714917, 3566793449, 3485975338, 3407193079, 3330382318, 3255481638, 3182432365, 3111178391, 3041666007, 2973843759, 2907662305, 2843074294, 2780034242, 2718498433, 2658424812, 2599772896, 2542503693, 2486579614, 2431964411, 2378623097, 2326521895, 2275628168, 2225910371, 2177337998, 2129881534, 2083512407, 2038202953, 1993926369, 1950656679, 1908368703, 1867038016, 1826640925, 1787154434, 1748556222, 1710824610, 1673938544, 1637877566, 1602621795, 1568151904, 1534449101, 1501495111, 1469272157, 1437762942, 1406950635, 1376818852, 1347351646, 1318533487, 1290349254, 1262784216, 1235824025, 1209454703, 1183662627, 1158434522, 1133757448, 1109618791, 1086006255, 1062907849, 1040311879, 1018206942, 996581916, 975425950, 954728460, 934479117, 914667845, 895284811, 876320418, 857765299, 839610312, 821846532, 804465247, 787457951, 770816338, 754532300, 738597918, 723005458, 707747368, 692816271, 678204962, 663906403, 649913719, 636220194, 622819267, 609704526, 596869708, 584308693, 572015499, 559984284, 548209337, 536685074, 525406043, 514366912, 503562469, 492987622, 482637392, 472506913, 462591427, 452886283]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1233).prefactor = (683308886500799/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1233).cutoff/(generalMeanRows 1233).c)).2 =
    (100333157888019/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1233).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1233).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1233).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1233

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1233).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1233).criticalRate j.val*(generalMeanRows 1233).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1233).c*(generalMeanRows 1233).criticalPoint j.val)).2-
      (generalMeanRows 1233).J/2-(generalMeanRows 1233).error (generalMeanGrid j.val)+
      (generalMeanRows 1233).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1233).c)).2-
      (generalMeanRows 1233).J/2-(generalMeanRows 1233).error 4 := by
  have he : (generalMeanRows 1233).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1233) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1233)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1233

/-! Kernel-checked entropy margins for general spectral rectangle 1234. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1234
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5093160608, 4948117736, 4808277999, 4673364317, 4543121696, 4417314947, 4295726681, 4178155538, 4064414622, 3954330112, 3847740040, 3744493191, 3644448132, 3547472345, 3453441450, 3362238511, 3273753415, 3187882311, 3104527109, 3023595030, 2944998191, 2868653243, 2794481033, 2722406303, 2652357415, 2584266101, 2518067234, 2453698626, 2391100830, 2330216974, 2270992599, 2213375513, 2157315659, 2102764987, 2049677347, 1998008379, 1947715416, 1898757397, 1851094783, 1804689476, 1759504753, 1715505192, 1672656615, 1630926027, 1590281563, 1550692433, 1512128880, 1474562129, 1437964350, 1402308612, 1367568852, 1333719834, 1300737122, 1268597039, 1237276646, 1206753711, 1177006677, 1148014646, 1119757345, 1092215109, 1065368860, 1039200079, 1013690793, 988823556, 964581423, 940947943, 917907135, 895443475, 873541882, 852187699, 831366686, 811064999, 791269181, 771966152, 753143193, 734787936, 716888353, 699432746, 682409737, 665808258, 649617540, 633827106, 618426762, 603406588, 588756930, 574468392, 560531828, 546938337, 533679251, 520746136, 508130776, 495825175, 483821545, 472112303, 460690065, 449547639, 438678021, 428074389, 417730097, 407638674, 397793815, 388189375, 378819373, 369677977, 360759507, 352058429, 343569351, 335287017, 327206307, 319322231, 311629926, 304124652, 296801792, 289656843, 282685418, 275883240, 269246141, 262770058, 256451029, 250285194, 244268789]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1234).prefactor = (38355411575291/8000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1234).cutoff/(generalMeanRows 1234).c)).2 =
    (6521129819131/7812500000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1234).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1234).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1234).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1234

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1234).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1234).criticalRate j.val*(generalMeanRows 1234).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1234).c*(generalMeanRows 1234).criticalPoint j.val)).2-
      (generalMeanRows 1234).J/2-(generalMeanRows 1234).error (generalMeanGrid j.val)+
      (generalMeanRows 1234).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1234).c)).2-
      (generalMeanRows 1234).J/2-(generalMeanRows 1234).error 4 := by
  have he : (generalMeanRows 1234).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1234) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1234)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1234

/-! Kernel-checked entropy margins for general spectral rectangle 1235. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1235
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5479195847, 5328106882, 5182338345, 5041606756, 4905651405, 4774231988, 4647126535, 4524129573, 4405050506, 4289712186, 4177949634, 4069608918, 3964546140, 3862626544, 3763723713, 3667718849, 3574500138, 3483962167, 3396005408, 3310535752, 3227464091, 3146705931, 3068181055, 2991813209, 2917529819, 2845261738, 2774943008, 2706510647, 2639904460, 2575066857, 2511942689, 2450479104, 2390625406, 2332332930, 2275554925, 2220246450, 2166364272, 2113866774, 2062713874, 2012866942, 1964288729, 1916943299, 1870795966, 1825813232, 1781962734, 1739213194, 1697534365, 1656896991, 1617272761, 1578634271, 1540954985, 1504209198, 1468372006, 1433419269, 1399327586, 1366074265, 1333637293, 1301995315, 1271127607, 1241014052, 1211635123, 1182971854, 1155005828, 1127719155, 1101094450, 1075114823, 1049763856, 1025025593, 1000884517, 977325545, 954334006, 931895632, 909996545, 888623242, 867762587, 847401796, 827528430, 808130381, 789195862, 770713401, 752671828, 735060267, 717868128, 701085098, 684701132, 668706449, 653091518, 637847056, 622964022, 608433603, 594247214, 580396492, 566873282, 553669643, 540777831, 528190299, 515899694, 503898845, 492180762, 480738633, 469565815, 458655832, 448002369, 437599269, 427440528, 417520293, 407832854, 398372642, 389134229, 380112319, 371301745, 362697470, 354294579, 346088279, 338073893, 330246860, 322602730, 315137162, 307845919, 300724869, 293769981]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1235).prefactor = (2479274508062869/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1235).cutoff/(generalMeanRows 1235).c)).2 =
    (211867686917951/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1235).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1235).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1235).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1235

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1235).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1235).criticalRate j.val*(generalMeanRows 1235).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1235).c*(generalMeanRows 1235).criticalPoint j.val)).2-
      (generalMeanRows 1235).J/2-(generalMeanRows 1235).error (generalMeanGrid j.val)+
      (generalMeanRows 1235).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1235).c)).2-
      (generalMeanRows 1235).J/2-(generalMeanRows 1235).error 4 := by
  have he : (generalMeanRows 1235).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1235) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1235)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1235

/-! Kernel-checked entropy margins for general spectral rectangle 1236. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1236
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6050332286, 5894422268, 5743804982, 5598197247, 5457339000, 5320990872, 5188932070, 5060958496, 4936881094, 4816524385, 4699725163, 4586331349, 4476200959, 4369201189, 4265207601, 4164103392, 4065778740, 3970130219, 3877060271, 3786476734, 3698292412, 3612424695, 3528795207, 3447329495, 3367956739, 3290609496, 3215223467, 3141737276, 3070092281, 3000232392, 2932103910, 2865655377, 2800837438, 2737602716, 2675905696, 2615702621, 2556951388, 2499611463, 2443643794, 2389010733, 2335675965, 2283604441, 2232762315, 2183116883, 2134636536, 2087290702, 2041049802, 1995885207, 1951769192, 1908674900, 1866576307, 1825448182, 1785266061, 1746006211, 1707645602, 1670161883, 1633533353, 1597738936, 1562758160, 1528571133, 1495158523, 1462501538, 1430581906, 1399381859, 1368884113, 1339071854, 1309928720, 1281438790, 1253586563, 1226356953, 1199735266, 1173707196, 1148258809, 1123376530, 1099047135, 1075257740, 1051995788, 1029249043, 1007005575, 985253758, 963982256, 943180016, 922836261, 902940479, 883482418, 864452081, 845839714, 827635799, 809831054, 792416419, 775383056, 758722338, 742425846, 726485363, 710892869, 695640535, 680720717, 666125955, 651848964, 637882629, 624220007, 610854314, 597778928, 584987379, 572473352, 560230675, 548253321, 536535405, 525071174, 513855012, 502881430, 492145067, 481640684, 471363162, 461307501, 451468814, 441842326, 432423370, 423207386, 414189919, 405366612]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1236).prefactor = (2529853573596587/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1236).cutoff/(generalMeanRows 1236).c)).2 =
    (3494010345559/4000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1236).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1236).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1236).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1236

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1236).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1236).criticalRate j.val*(generalMeanRows 1236).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1236).c*(generalMeanRows 1236).criticalPoint j.val)).2-
      (generalMeanRows 1236).J/2-(generalMeanRows 1236).error (generalMeanGrid j.val)+
      (generalMeanRows 1236).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1236).c)).2-
      (generalMeanRows 1236).J/2-(generalMeanRows 1236).error 4 := by
  have he : (generalMeanRows 1236).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1236) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1236)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1236

/-! Kernel-checked entropy margins for general spectral rectangle 1237. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1237
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5817749846, 5660827647, 5509363762, 5363067098, 5221670067, 5084926139, 4952607695, 4824504129, 4700420169, 4580174400, 4463597943, 4350533288, 4240833254, 4134360061, 4030984502, 3930585205, 3833047962, 3738265144, 3646135158, 3556561967, 3469454661, 3384727058, 3302297353, 3222087799, 3144024412, 3068036710, 2994057472, 2922022515, 2851870500, 2783542745, 2716983062, 2652137597, 2588954697, 2527384775, 2467380193, 2408895155, 2351885599, 2296309109, 2242124827, 2189293371, 2137776760, 2087538346, 2038542750, 1990755797, 1944144466, 1898676831, 1854322017, 1811050149, 1768832312, 1727640509, 1687447621, 1648227373, 1609954298, 1572603708, 1536151658, 1500574921, 1465850962, 1431957907, 1398874524, 1366580196, 1335054898, 1304279181, 1274234145, 1244901426, 1216263173, 1188302034, 1161001137, 1134344074, 1108314889, 1082898058, 1058078479, 1033841457, 1010172693, 987058269, 964484636, 942438606, 920907337, 899878327, 879339398, 859278690, 839684653, 820546034, 801851871, 783591482, 765754461, 748330665, 731310212, 714683469, 698441046, 682573792, 667072785, 651929326, 637134935, 622681343, 608560487, 594764505, 581285729, 568116680, 555250066, 542678771, 530395857, 518394554, 506668258, 495210527, 484015076, 473075772, 462386632, 451941816, 441735629, 431762510, 422017034, 412493906, 403187958, 394094148, 385207553, 376523368, 368036903, 359743581, 351638933, 343718596, 335978313]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1237).prefactor = (2564144910509669/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1237).cutoff/(generalMeanRows 1237).c)).2 =
    (214018237813617/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1237).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1237).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1237).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1237

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1237).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1237).criticalRate j.val*(generalMeanRows 1237).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1237).c*(generalMeanRows 1237).criticalPoint j.val)).2-
      (generalMeanRows 1237).J/2-(generalMeanRows 1237).error (generalMeanGrid j.val)+
      (generalMeanRows 1237).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1237).c)).2-
      (generalMeanRows 1237).J/2-(generalMeanRows 1237).error 4 := by
  have he : (generalMeanRows 1237).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1237) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1237)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1237

/-! Kernel-checked entropy margins for general spectral rectangle 1238. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1238
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5938292540, 5776331424, 5620038585, 5469111888, 5323273529, 5182267510, 5045857412, 4913824440, 4785965684, 4662092589, 4542029594, 4425612920, 4312689501, 4203116018, 4096758044, 3993489281, 3893190868, 3795750770, 3701063221, 3609028227, 3519551116, 3432542133, 3347916071, 3265591940, 3185492667, 3107544820, 3031678358, 2957826406, 2885925047, 2815913133, 2747732109, 2681325859, 2616640552, 2553624518, 2492228117, 2432403624, 2374105132, 2317288444, 2261910992, 2207931747, 2155311143, 2104011006, 2053994485, 2005225991, 1957671133, 1911296672, 1866070461, 1821961400, 1778939393, 1736975301, 1696040905, 1656108866, 1617152692, 1579146703, 1542065997, 1505886423, 1470584552, 1436137648, 1402523643, 1369721115, 1337709260, 1306467875, 1275977334, 1246218568, 1217173046, 1188822758, 1161150196, 1134138337, 1107770630, 1082030976, 1056903717, 1032373620, 1008425865, 985046032, 962220084, 939934364, 918175574, 896930771, 876187351, 855933045, 836155901, 816844282, 797986853, 779572573, 761590686, 744030713, 726882445, 710135934, 693781486, 677809653, 662211229, 646977240, 632098939, 617567800, 603375510, 589513966, 575975267, 562751711, 549835785, 537220166, 524897710, 512861453, 501104600, 489620526, 478402769, 467445024, 456741143, 446285128, 436071128, 426093433, 416346474, 406824818, 397523164, 388436338, 379559294, 370887105, 362414966, 354138186, 346052189, 338152509, 330434785]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1238).prefactor = (5303841184758327/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1238).cutoff/(generalMeanRows 1238).c)).2 =
    (170352519950669/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1238).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1238).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1238).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1238

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1238).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1238).criticalRate j.val*(generalMeanRows 1238).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1238).c*(generalMeanRows 1238).criticalPoint j.val)).2-
      (generalMeanRows 1238).J/2-(generalMeanRows 1238).error (generalMeanGrid j.val)+
      (generalMeanRows 1238).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1238).c)).2-
      (generalMeanRows 1238).J/2-(generalMeanRows 1238).error 4 := by
  have he : (generalMeanRows 1238).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1238) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1238)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1238

/-! Kernel-checked entropy margins for general spectral rectangle 1239. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1239
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6473521150, 6304757140, 6141756957, 5984212522, 5831840835, 5684381353, 5541593692, 5403255592, 5269161121, 5139119089, 5012951643, 4890493009, 4771588384, 4656092944, 4543870959, 4434794999, 4328745226, 4225608762, 4125279113, 4027655656, 3932643179, 3840151460, 3750094893, 3662392140, 3576965830, 3493742270, 3412651194, 3333625527, 3256601176, 3181516835, 3108313805, 3036935836, 2967328976, 2899441432, 2833223447, 2768627186, 2705606622, 2644117444, 2584116961, 2525564021, 2468418928, 2412643372, 2358200361, 2305054155, 2253170209, 2202515118, 2153056563, 2104763265, 2057604938, 2011552246, 1966576766, 1922650945, 1879748069, 1837842229, 1796908284, 1756921839, 1717859211, 1679697403, 1642414080, 1605987544, 1570396711, 1535621089, 1501640758, 1468436347, 1435989021, 1404280456, 1373292829, 1343008794, 1313411473, 1284484436, 1256211689, 1228577660, 1201567186, 1175165499, 1149358214, 1124131320, 1099471162, 1075364440, 1051798190, 1028759778, 1006236889, 984217520, 962689968, 941642821, 921064955, 900945519, 881273933, 862039875, 843233279, 824844325, 806863433, 789281257, 772088676, 755276792, 738836922, 722760590, 707039526, 691665657, 676631104, 661928175, 647549361, 633487333, 619734934, 606285176, 593131238, 580266457, 567684328, 555378499, 543342766, 531571070, 520057494, 508796258, 497781717, 487008356, 476470789, 466163754, 456082110, 446220837, 436575028, 427139889, 417910738]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1239).prefactor = (1371350503526491/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1239).cutoff/(generalMeanRows 1239).c)).2 =
    (173823322889299/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1239).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1239).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1239).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1239

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1239).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1239).criticalRate j.val*(generalMeanRows 1239).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1239).c*(generalMeanRows 1239).criticalPoint j.val)).2-
      (generalMeanRows 1239).J/2-(generalMeanRows 1239).error (generalMeanGrid j.val)+
      (generalMeanRows 1239).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1239).c)).2-
      (generalMeanRows 1239).J/2-(generalMeanRows 1239).error 4 := by
  have he : (generalMeanRows 1239).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1239) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1239)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1239

/-! Kernel-checked entropy margins for general spectral rectangle 1240. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1240
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6965168510, 6789878283, 6620467752, 6456621586, 6298050338, 6144487732, 5995688276, 5851425156, 5711488377, 5575683122, 5443828290, 5315755206, 5191306466, 5070334911, 4952702715, 4838280563, 4726946921, 4618587379, 4513094058, 4410365085, 4310304110, 4212819878, 4117825842, 4025239804, 3934983604, 3846982823, 3761166528, 3677467024, 3595819644, 3516162545, 3438436525, 3362584863, 3288553158, 3216289196, 3145742817, 3076865796, 3009611738, 2943935972, 2879795461, 2817148713, 2755955705, 2696177801, 2637777693, 2580719328, 2524967850, 2470489549, 2417251801, 2365223023, 2314372629, 2264670982, 2216089357, 2168599901, 2122175598, 2076790237, 2032418376, 1989035314, 1946617064, 1905140324, 1864582451, 1824921438, 1786135893, 1748205011, 1711108559, 1674826854, 1639340744, 1604631590, 1570681249, 1537472058, 1504986817, 1473208777, 1442121621, 1411709455, 1381956791, 1352848536, 1324369981, 1296506788, 1269244979, 1242570924, 1216471334, 1190933247, 1165944023, 1141491331, 1117563139, 1094147712, 1071233598, 1048809619, 1026864870, 1005388705, 984370733, 963800810, 943669033, 923965734, 904681472, 885807029, 867333400, 849251795, 831553625, 814230503, 797274235, 780676817, 764430430, 748527434, 732960363, 717721926, 702804994, 688202604, 673907949, 659914377, 646215386, 632804624, 619675878, 606823078, 594240288, 581921707, 569861663, 558054611, 546495129, 535177916, 524097791, 513249684, 502628641]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1240).prefactor = (354573626549501/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1240).cutoff/(generalMeanRows 1240).c)).2 =
    (882332665838021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1240).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1240).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1240).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1240

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1240).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1240).criticalRate j.val*(generalMeanRows 1240).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1240).c*(generalMeanRows 1240).criticalPoint j.val)).2-
      (generalMeanRows 1240).J/2-(generalMeanRows 1240).error (generalMeanGrid j.val)+
      (generalMeanRows 1240).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1240).c)).2-
      (generalMeanRows 1240).J/2-(generalMeanRows 1240).error 4 := by
  have he : (generalMeanRows 1240).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1240) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1240)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1240

/-! Kernel-checked entropy margins for general spectral rectangle 1241. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1241
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7524534556, 7346495399, 7174255948, 7007502596, 6845947848, 6689327567, 6537398553, 6389936403, 6246733631, 6107597999, 5972351036, 5840826733, 5712870371, 5588337483, 5467092932, 5349010079, 5233970042, 5121861037, 5012577776, 4906020938, 4802096683, 4700716219, 4601795408, 4505254417, 4411017390, 4319012163, 4229169996, 4141425337, 4055715598, 3971980959, 3890164188, 3810210469, 3732067254, 3655684124, 3581012656, 3508006308, 3436620313, 3366811572, 3298538568, 3231761276, 3166441089, 3102540737, 3040024226, 2978856771, 2919004735, 2860435581, 2803117812, 2747020929, 2692115385, 2638372541, 2585764628, 2534264709, 2483846645, 2434485064, 2386155324, 2338833492, 2292496311, 2247121173, 2202686100, 2159169716, 2116551225, 2074810394, 2033927528, 1993883454, 1954659503, 1916237492, 1878599708, 1841728889, 1805608218, 1770221298, 1735552146, 1701585177, 1668305192, 1635697364, 1603747232, 1572440685, 1541763951, 1511703592, 1482246491, 1453379840, 1425091137, 1397368172, 1370199022, 1343572043, 1317475859, 1291899358, 1266831683, 1242262226, 1218180620, 1194576734, 1171440667, 1148762741, 1126533493, 1104743674, 1083384240, 1062446350, 1041921356, 1021800803, 1002076419, 982740118, 963783986, 945200286, 926981445, 909120056, 891608874, 874440807, 857608918, 841106417, 824926660, 809063144, 793509507, 778259520, 763307085, 748646236, 734271131, 720176051, 706355397, 692803690, 679515562, 666485759, 653709138]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1241).prefactor = (2868593872634413/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1241).cutoff/(generalMeanRows 1241).c)).2 =
    (452377564946927/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1241).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1241).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1241).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1241

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1241).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1241).criticalRate j.val*(generalMeanRows 1241).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1241).c*(generalMeanRows 1241).criticalPoint j.val)).2-
      (generalMeanRows 1241).J/2-(generalMeanRows 1241).error (generalMeanGrid j.val)+
      (generalMeanRows 1241).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1241).c)).2-
      (generalMeanRows 1241).J/2-(generalMeanRows 1241).error 4 := by
  have he : (generalMeanRows 1241).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1241) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1241)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1241

/-! Kernel-checked entropy margins for general spectral rectangle 1242. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1242
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5761540711, 5587060911, 5419077949, 5257245268, 5101243542, 4950777895, 4805575448, 4665383151, 4529965870, 4399104693, 4272595418, 4150247219, 4031881450, 3917330577, 3806437229, 3699053342, 3595039395, 3494263720, 3396601884, 3301936130, 3210154872, 3121152240, 3034827666, 2951085508, 2869834709, 2790988490, 2714464060, 2640182366, 2568067850, 2498048234, 2430054321, 2364019816, 2299881153, 2237577339, 2177049817, 2118242328, 2061100792, 2005573190, 1951609462, 1899161409, 1848182598, 1798628279, 1750455305, 1703622057, 1658088375, 1613815490, 1570765964, 1528903635, 1488193556, 1448601949, 1410096155, 1372644587, 1336216688, 1300782890, 1266314575, 1232784038, 1200164451, 1168429833, 1137555014, 1107515609, 1078287986, 1049849242, 1022177174, 995250256, 969047613, 943549003, 918734788, 894585921, 871083920, 848210852, 825949314, 804282415, 783193760, 762667433, 742687982, 723240402, 704310126, 685883002, 667945291, 650483644, 633485096, 616937051, 600827272, 585143871, 569875292, 555010312, 540538019, 526447811, 512729382, 499372715, 486368075, 473705996, 461377277, 449372972, 437684384, 426303057, 415220767, 404429520, 393921540, 383689266, 373725344, 364022623, 354574147, 345373150, 336413052, 327687451, 319190122, 310915007, 302856214, 295008009, 287364817, 279921211, 272671911, 265611782, 258735826, 252039179, 245517111, 239165015, 232978412, 226952942, 221084361]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1242).prefactor = (2933690987298463/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1242).cutoff/(generalMeanRows 1242).c)).2 =
    (809651114403219/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1242).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1242).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1242).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1242

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1242).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1242).criticalRate j.val*(generalMeanRows 1242).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1242).c*(generalMeanRows 1242).criticalPoint j.val)).2-
      (generalMeanRows 1242).J/2-(generalMeanRows 1242).error (generalMeanGrid j.val)+
      (generalMeanRows 1242).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1242).c)).2-
      (generalMeanRows 1242).J/2-(generalMeanRows 1242).error 4 := by
  have he : (generalMeanRows 1242).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1242) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1242)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1242

/-! Kernel-checked entropy margins for general spectral rectangle 1243. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1243
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6680737607, 6498527028, 6322693413, 6152896850, 5988824804, 5830189269, 5676724268, 5528183651, 5384339138, 5244978599, 5109904525, 4978932660, 4851890799, 4728617706, 4608962147, 4492782031, 4379943640, 4270320929, 4163794909, 4060253084, 3959588947, 3861701518, 3766494939, 3673878095, 3583764275, 3496070866, 3410719071, 3327633654, 3246742707, 3167977434, 3091271963, 3016563158, 2943790462, 2872895742, 2803823151, 2736519001, 2670931641, 2607011351, 2544710239, 2483982147, 2424782563, 2367068540, 2310798619, 2255932761, 2202432277, 2150259771, 2099379076, 2049755205, 2001354299, 1954143575, 1908091287, 1863166677, 1819339942, 1776582190, 1734865406, 1694162420, 1654446873, 1615693186, 1577876533, 1540972813, 1504958622, 1469811231, 1435508558, 1402029152, 1369352165, 1337457334, 1306324963, 1275935901, 1246271526, 1217313728, 1189044891, 1161447878, 1134506014, 1108203077, 1082523277, 1057451247, 1032972028, 1009071057, 985734157, 962947521, 940697706, 918971620, 897756509, 877039953, 856809850, 837054412, 817762152, 798921880, 780522689, 762553951, 745005308, 727866664, 711128178, 694780258, 678813553, 663218946, 647987549, 633110695, 618579934, 604387025, 590523934, 576982823, 563756050, 550836160, 538215884, 525888129, 513845977, 502082681, 490591658, 479366484, 468400896, 457688779, 447224170, 437001248, 427014336, 417257892, 407726509, 398414912, 389317950, 380430598, 371747953]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1243).prefactor = (5966962898192207/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1243).cutoff/(generalMeanRows 1243).c)).2 =
    (170352519950669/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1243).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1243).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1243).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1243

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1243).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1243).criticalRate j.val*(generalMeanRows 1243).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1243).c*(generalMeanRows 1243).criticalPoint j.val)).2-
      (generalMeanRows 1243).J/2-(generalMeanRows 1243).error (generalMeanGrid j.val)+
      (generalMeanRows 1243).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1243).c)).2-
      (generalMeanRows 1243).J/2-(generalMeanRows 1243).error 4 := by
  have he : (generalMeanRows 1243).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1243) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1243)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1243

/-! Kernel-checked entropy margins for general spectral rectangle 1244. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1244
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6469673579, 6302633294, 6141287460, 5985330392, 5834481308, 5688481737, 5547093243, 5410095411, 5277284069, 5148469716, 5023476121, 4902139082, 4784305321, 4669831495, 4558583320, 4450434777, 4345267409, 4242969687, 4143436439, 4046568338, 3952271440, 3860456768, 3771039931, 3683940786, 3599083128, 3516394407, 3435805475, 3357250350, 3280666008, 3205992184, 3133171201, 3062147802, 2992869003, 2925283958, 2859343832, 2795001685, 2732212365, 2670932411, 2611119959, 2552734660, 2495737599, 2440091227, 2385759286, 2332706755, 2280899781, 2230305634, 2180892648, 2132630178, 2085488551, 2039439027, 1994453759, 1950505753, 1907568835, 1865617618, 1824627470, 1784574484, 1745435451, 1707187834, 1669809739, 1633279898, 1597577639, 1562682873, 1528576063, 1495238215, 1462650851, 1430795998, 1399656167, 1369214337, 1339453942, 1310358856, 1281913374, 1254102206, 1226910459, 1200323626, 1174327574, 1148908533, 1124053083, 1099748147, 1075980979, 1052739153, 1030010554, 1007783372, 986046089, 964787473, 943996569, 923662694, 903775423, 884324589, 865300271, 846692789, 828492698, 810690780, 793278040, 776245696, 759585180, 743288125, 727346365, 711751927, 696497027, 681574064, 666975617, 652694439, 638723453, 625055747, 611684572, 598603334, 585805594, 573285061, 561035591, 549051181, 537325968, 525854221, 514630344, 503648868, 492904449, 482391866, 472106016, 462041913, 452194686, 442559572, 433131918]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1244).prefactor = (1351567035880261/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1244).cutoff/(generalMeanRows 1244).c)).2 =
    (17182276978753/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1244).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1244).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1244).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1244

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1244).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1244).criticalRate j.val*(generalMeanRows 1244).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1244).c*(generalMeanRows 1244).criticalPoint j.val)).2-
      (generalMeanRows 1244).J/2-(generalMeanRows 1244).error (generalMeanGrid j.val)+
      (generalMeanRows 1244).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1244).c)).2-
      (generalMeanRows 1244).J/2-(generalMeanRows 1244).error 4 := by
  have he : (generalMeanRows 1244).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1244) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1244)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1244

/-! Kernel-checked entropy margins for general spectral rectangle 1245. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1245
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6102248912, 5956720534, 5815837129, 5679356799, 5547057535, 5418735092, 5294201110, 5173281482, 5055814907, 4941651620, 4830652265, 4722686905, 4617634139, 4515380319, 4415818853, 4318849584, 4224378240, 4132315931, 4042578710, 3955087172, 3869766096, 3786544122, 3705353458, 3626129621, 3548811191, 3473339602, 3399658942, 3327715776, 3257458979, 3188839592, 3121810684, 3056327227, 2992345982, 2929825393, 2868725494, 2809007813, 2750635297, 2693572232, 2637784171, 2583237874, 2529901240, 2477743258, 2426733950, 2376844320, 2328046314, 2280312774, 2233617396, 2187934695, 2143239968, 2099509264, 2056719348, 2014847676, 1973872362, 1933772158, 1894526424, 1856115109, 1818518725, 1781718327, 1745695494, 1710432310, 1675911345, 1642115639, 1609028683, 1576634409, 1544917169, 1513861723, 1483453228, 1453677223, 1424519616, 1395966672, 1368005005, 1340621562, 1313803617, 1287538761, 1261814887, 1236620189, 1211943146, 1187772516, 1164097331, 1140906884, 1118190725, 1095938652, 1074140705, 1052787158, 1031868514, 1011375499, 991299052, 971630324, 952360670, 933481645, 914984995, 896862658, 879106752, 861709576, 844663602, 827961473, 811595996, 795560140, 779847030, 764449944, 749362312, 734577705, 720089839, 705892569, 691979882, 678345899, 664984869, 651891166, 639059286, 626483847, 614159580, 602081332, 590244061, 578642833, 567272820, 556129297, 545207641, 534503327, 524011928, 513729108, 503650626]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1245).prefactor = (4664409679116481/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1245).cutoff/(generalMeanRows 1245).c)).2 =
    (193775931612679/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1245).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1245).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1245).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1245

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1245).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1245).criticalRate j.val*(generalMeanRows 1245).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1245).c*(generalMeanRows 1245).criticalPoint j.val)).2-
      (generalMeanRows 1245).J/2-(generalMeanRows 1245).error (generalMeanGrid j.val)+
      (generalMeanRows 1245).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1245).c)).2-
      (generalMeanRows 1245).J/2-(generalMeanRows 1245).error 4 := by
  have he : (generalMeanRows 1245).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1245) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1245)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1245

/-! Kernel-checked entropy margins for general spectral rectangle 1246. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1246
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4814048860, 4669614163, 4530432946, 4396233635, 4266765739, 4141797666, 4021114801, 3904517818, 3791821192, 3682851886, 3577448187, 3475458671, 3376741292, 3281162562, 3188596823, 3098925597, 3012037002, 2927825228, 2846190069, 2767036497, 2690274282, 2615817642, 2543584935, 2473498371, 2405483755, 2339470252, 2275390171, 2213178769, 2152774072, 2094116709, 2037149760, 1981818617, 1928070855, 1875856113, 1825125985, 1775833915, 1727935103, 1681386420, 1636146323, 1592174778, 1549433189, 1507884334, 1467492296, 1428222413, 1390041212, 1352916367, 1316816644, 1281711859, 1247572828, 1214371334, 1182080082, 1150672666, 1120123532, 1090407945, 1061501958, 1033382382, 1006026757, 979413328, 953521014, 928329388, 903818651, 879969610, 856763657, 834182750, 812209390, 790826604, 770017930, 749767392, 730059494, 710879195, 692211898, 674043436, 656360055, 639148405, 622395522, 606088819, 590216072, 574765411, 559725305, 545084556, 530832285, 516957923, 503451201, 490302144, 477501057, 465038520, 452905377, 441092733, 429591938, 418394588, 407492513, 396877769, 386542637, 376479608, 366681385, 357140872, 347851169, 338805567, 329997541, 321420747, 313069014, 304936342, 297016893, 289304992, 281795116, 274481894, 267360103, 260424659, 253670620, 247093174, 240687643, 234449475, 228374240, 222457629, 216695448, 211083619, 205618170, 200295240, 195111069, 190061999, 185144471]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1246).prefactor = (4827417770817311/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1246).cutoff/(generalMeanRows 1246).c)).2 =
    (440107010488869/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1246).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1246).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1246).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1246

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1246).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1246).criticalRate j.val*(generalMeanRows 1246).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1246).c*(generalMeanRows 1246).criticalPoint j.val)).2-
      (generalMeanRows 1246).J/2-(generalMeanRows 1246).error (generalMeanGrid j.val)+
      (generalMeanRows 1246).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1246).c)).2-
      (generalMeanRows 1246).J/2-(generalMeanRows 1246).error 4 := by
  have he : (generalMeanRows 1246).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1246) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1246)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1246

/-! Kernel-checked entropy margins for general spectral rectangle 1247. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1247
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5313863232, 5162215098, 5015911685, 4874677427, 4738258416, 4606420135, 4478945469, 4355632960, 4236295267, 4120757807, 4008857553, 3900441969, 3795368064, 3693501550, 3594716092, 3498892637, 3405918814, 3315688399, 3228100828, 3143060764, 3060477707, 2980265635, 2902342690, 2826630882, 2753055830, 2681546519, 2612035081, 2544456596, 2478748913, 2414852475, 2352710172, 2292267198, 2233470916, 2176270746, 2120618049, 2066466024, 2013769614, 1962485418, 1912571608, 1863987852, 1816695244, 1770656232, 1725834566, 1682195227, 1639704380, 1598329322, 1558038429, 1518801116, 1480587788, 1443369803, 1407119435, 1371809833, 1337414991, 1303909711, 1271269577, 1239470921, 1208490798, 1178306960, 1148897826, 1120242464, 1092320564, 1065112416, 1038598893, 1012761425, 987581985, 963043067, 939127673, 915819290, 893101880, 870959859, 849378086, 828341849, 807836847, 787849183, 768365345, 749372200, 730856976, 712807257, 695210968, 678056364, 661332023, 645026836, 629129994, 613630983, 598519574, 583785813, 569420014, 555412753, 541754857, 528437399, 515451690, 502789273, 490441914, 478401599, 466660526, 455211098, 444045919, 433157787, 422539690, 412184798, 402086463, 392238207, 382633723, 373266868, 364131659, 355222267, 346533016, 338058376, 329792959, 321731518, 313868940, 306200243, 298720576, 291425209, 284309535, 277369065, 270599426, 263996355, 257555698, 251273408, 245145541]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1247).prefactor = (4996122540080347/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1247).cutoff/(generalMeanRows 1247).c)).2 =
    (900622892608943/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1247).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1247).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1247).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1247

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1247).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1247).criticalRate j.val*(generalMeanRows 1247).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1247).c*(generalMeanRows 1247).criticalPoint j.val)).2-
      (generalMeanRows 1247).J/2-(generalMeanRows 1247).error (generalMeanGrid j.val)+
      (generalMeanRows 1247).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1247).c)).2-
      (generalMeanRows 1247).J/2-(generalMeanRows 1247).error 4 := by
  have he : (generalMeanRows 1247).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1247) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1247)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1247

/-! Kernel-checked entropy margins for general spectral rectangle 1248. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1248
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5786249654, 5629597624, 5478295724, 5332068138, 5190661018, 5053840162, 4921388986, 4793106740, 4668806931, 4548315942, 4431471803, 4318123103, 4208128031, 4101353515, 3997674460, 3896973064, 3799138214, 3704064934, 3611653899, 3521810991, 3434446906, 3349476794, 3266819935, 3186399445, 3108142012, 3031977655, 2957839500, 2885663583, 2815388666, 2746956065, 2680309504, 2615394966, 2552160568, 2490556438, 2430534608, 2372048906, 2315054867, 2259509645, 2205371925, 2152601856, 2101160974, 2051012138, 2002119468, 1954448290, 1907965077, 1862637404, 1818433895, 1775324182, 1733278861, 1692269455, 1652268371, 1613248871, 1575185035, 1538051727, 1501824572, 1466479920, 1431994823, 1398347008, 1365514854, 1333477366, 1302214156, 1271705419, 1241931913, 1212874943, 1184516338, 1156838437, 1129824070, 1103456541, 1077719617, 1052597507, 1028074854, 1004136716, 980768555, 957956226, 935685961, 913944362, 892718386, 871995337, 851762852, 832008896, 812721747, 793889991, 775502510, 757548476, 740017341, 722898828, 706182925, 689859877, 673920179, 658354568, 643154017, 628309728, 613813126, 599655851, 585829757, 572326899, 559139535, 546260114, 533681276, 521395842, 509396813, 497677364, 486230839, 475050746, 464130754, 453464688, 443046526, 432870391, 422930553, 413221421, 403737541, 394473593, 385424386, 376584854, 367950056, 359515172, 351275495, 343226436, 335363514, 327682358, 320178703]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1248).prefactor = (2550081169374849/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1248).cutoff/(generalMeanRows 1248).c)).2 =
    (184291395902357/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1248).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1248).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1248).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1248

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1248).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1248).criticalRate j.val*(generalMeanRows 1248).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1248).c*(generalMeanRows 1248).criticalPoint j.val)).2-
      (generalMeanRows 1248).J/2-(generalMeanRows 1248).error (generalMeanGrid j.val)+
      (generalMeanRows 1248).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1248).c)).2-
      (generalMeanRows 1248).J/2-(generalMeanRows 1248).error 4 := by
  have he : (generalMeanRows 1248).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1248) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1248)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1248

/-! Kernel-checked entropy margins for general spectral rectangle 1249. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1249
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5790990332, 5632512901, 5479482013, 5331616937, 5188659238, 5050370429, 4916529913, 4786933174, 4661390179, 4539723979, 4421769461, 4307372246, 4196387716, 4088680142, 3984121909, 3882592825, 3783979502, 3688174804, 3595077348, 3504591056, 3416624754, 3331091808, 3247909793, 3167000197, 3088288153, 3011702188, 2937174004, 2864638269, 2794032438, 2725296574, 2658373197, 2593207137, 2529745405, 2467937066, 2407733132, 2349086454, 2291951626, 2236284896, 2182044085, 2129188506, 2077678892, 2027477334, 1978547212, 1930853137, 1884360899, 1839037415, 1794850676, 1751769705, 1709764514, 1668806061, 1628866214, 1589917713, 1551934138, 1514889873, 1478760079, 1443520661, 1409148244, 1375620145, 1342914347, 1311009474, 1279884774, 1249520091, 1219895847, 1190993021, 1162793133, 1135278222, 1108430832, 1082233991, 1056671202, 1031726421, 1007384045, 983628901, 960446225, 937821658, 915741227, 894191336, 873158752, 852630598, 832594338, 813037770, 793949015, 775316504, 757128977, 739375464, 722045285, 705128036, 688613584, 672492059, 656753846, 641389575, 626390119, 611746586, 597450309, 583492843, 569865958, 556561633, 543572050, 530889589, 518506823, 506416510, 494611592, 483085187, 471830585, 460841246, 450110791, 439633001, 429401810, 419411306, 409655719, 400129425, 390826939, 381742911, 372872121, 364209480, 355750022, 347488906, 339421406, 331542913, 323848932, 316335076, 308997066]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1249).prefactor = (2585361534938461/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1249).cutoff/(generalMeanRows 1249).c)).2 =
    (917255292658087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1249).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1249).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1249).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1249

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1249).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1249).criticalRate j.val*(generalMeanRows 1249).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1249).c*(generalMeanRows 1249).criticalPoint j.val)).2-
      (generalMeanRows 1249).J/2-(generalMeanRows 1249).error (generalMeanGrid j.val)+
      (generalMeanRows 1249).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1249).c)).2-
      (generalMeanRows 1249).J/2-(generalMeanRows 1249).error 4 := by
  have he : (generalMeanRows 1249).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1249) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1249)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1249

/-! Kernel-checked entropy margins for general spectral rectangle 1250. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1250
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5993369271, 5829353497, 5670974607, 5517942059, 5369988387, 5226866771, 5088348903, 4954223119, 4824292748, 4698374654, 4576297954, 4457902876, 4343039748, 4231568095, 4123355843, 4018278601, 3916219018, 3817066213, 3720715261, 3627066726, 3536026247, 3447504163, 3361415169, 3277678010, 3196215199, 3116952769, 3039820032, 2964749377, 2891676069, 2820538078, 2751275916, 2683832485, 2618152942, 2554184575, 2491876681, 2431180465, 2372048934, 2314436808, 2258300432, 2203597698, 2150287967, 2098332005, 2047691911, 1998331061, 1950214050, 1903306637, 1857575694, 1812989164, 1769516008, 1727126172, 1685790539, 1645480897, 1606169902, 1567831043, 1530438613, 1493967677, 1458394040, 1423694228, 1389845452, 1356825594, 1324613173, 1293187329, 1262527800, 1232614901, 1203429506, 1174953025, 1147167394, 1120055047, 1093598909, 1067782378, 1042589304, 1018003984, 994011139, 970595906, 947743826, 925440826, 903673212, 882427656, 861691185, 841451170, 821695315, 802411651, 783588520, 765214571, 747278751, 729770291, 712678706, 695993779, 679705558, 663804349, 648280705, 633125421, 618329529, 603884288, 589781182, 576011908, 562568375, 549442698, 536627188, 524114352, 511896885, 499967665, 488319747, 476946361, 465840907, 454996947, 444408205, 434068559, 423972042, 414112831, 404485249, 395083759, 385902960, 376937584, 368182492, 359632673, 351283236, 343129412, 335166547, 327390103, 319795650]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1250).prefactor = (1070285080114447/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1250).cutoff/(generalMeanRows 1250).c)).2 =
    (917255292658087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1250).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1250).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1250).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1250

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1250).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1250).criticalRate j.val*(generalMeanRows 1250).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1250).c*(generalMeanRows 1250).criticalPoint j.val)).2-
      (generalMeanRows 1250).J/2-(generalMeanRows 1250).error (generalMeanGrid j.val)+
      (generalMeanRows 1250).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1250).c)).2-
      (generalMeanRows 1250).J/2-(generalMeanRows 1250).error 4 := by
  have he : (generalMeanRows 1250).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1250) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1250)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1250

/-! Kernel-checked entropy margins for general spectral rectangle 1251. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1251
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6448085960, 6277295551, 6112265612, 5952698955, 5798322194, 5648883222, 5504149007, 5363903653, 5227946686, 5096091558, 4968164305, 4844002374, 4723453575, 4606375154, 4492632957, 4382100699, 4274659298, 4170196285, 4068605273, 3969785478, 3873641293, 3780081896, 3689020904, 3600376051, 3514068905, 3430024604, 3348171618, 3268441536, 3190768863, 3115090842, 3041347287, 2969480431, 2899434787, 2831157016, 2764595812, 2699701789, 2636427379, 2574726741, 2514555670, 2455871518, 2398633117, 2342800706, 2288335871, 2235201477, 2183361615, 2132781544, 2083427642, 2035267360, 1988269173, 1942402539, 1897637862, 1853946449, 1811300481, 1769672971, 1729037740, 1689369379, 1650643228, 1612835343, 1575922470, 1539882026, 1504692067, 1470331273, 1436778922, 1404014871, 1372019537, 1340773877, 1310259370, 1280458002, 1251352248, 1222925055, 1195159831, 1168040425, 1141551119, 1115676608, 1090401995, 1065712771, 1041594809, 1018034348, 995017987, 972532669, 950565676, 929104613, 908137406, 887652287, 867637787, 848082728, 828976214, 810307624, 792066604, 774243057, 756827141, 739809257, 723180045, 706930379, 691051354, 675534288, 660370713, 645552365, 631071187, 616919315, 603089079, 589572994, 576363758, 563454246, 550837505, 538506748, 526455354, 514676861, 503164962, 491913499, 480916464, 470167992, 459662357, 449393970, 439357375, 429547246, 419958382, 410585706, 401424262, 392469208, 383715820]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1251).prefactor = (553844277306681/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1251).cutoff/(generalMeanRows 1251).c)).2 =
    (116239211191251/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1251).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1251).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1251).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1251

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1251).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1251).criticalRate j.val*(generalMeanRows 1251).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1251).c*(generalMeanRows 1251).criticalPoint j.val)).2-
      (generalMeanRows 1251).J/2-(generalMeanRows 1251).error (generalMeanGrid j.val)+
      (generalMeanRows 1251).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1251).c)).2-
      (generalMeanRows 1251).J/2-(generalMeanRows 1251).error 4 := by
  have he : (generalMeanRows 1251).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1251) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1251)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1251

/-! Kernel-checked entropy margins for general spectral rectangle 1252. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1252
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7028077194, 6850165374, 6678107196, 6511599792, 6350364827, 6194145892, 6042706211, 5895826633, 5753303861, 5614948893, 5480585641, 5350049716, 5223187338, 5099854380, 4979915508, 4863243422, 4749718167, 4639226528, 4531661478, 4426921689, 4324911091, 4225538466, 4128717094, 4034364427, 3942401789, 3852754112, 3765349691, 3680119960, 3596999294, 3515924820, 3436836246, 3359675712, 3284387640, 3210918607, 3139217225, 3069234022, 3000921348, 2934233272, 2869125499, 2805555283, 2743481352, 2682863837, 2623664207, 2565845202, 2509370781, 2454206061, 2400317273, 2347671707, 2296237672, 2245984451, 2196882263, 2148902222, 2102016305, 2056197317, 2011418856, 1967655289, 1924881718, 1883073956, 1842208499, 1802262502, 1763213757, 1725040669, 1687722238, 1651238032, 1615568176, 1580693327, 1546594661, 1513253852, 1480653059, 1448774909, 1417602484, 1387119304, 1357309314, 1328156874, 1299646742, 1271764066, 1244494367, 1217823534, 1191737810, 1166223782, 1141268370, 1116858819, 1092982690, 1069627848, 1046782459, 1024434974, 1002574129, 981188930, 960268652, 939802826, 919781237, 900193913, 881031120, 862283356, 843941348, 825996037, 808438582, 791260350, 774452909, 758008026, 741917661, 726173960, 710769255, 695696051, 680947032, 666515048, 652393115, 638574409, 625052265, 611820170, 598871758, 586200811, 573801253, 561667145, 549792683, 538172197, 526800142, 515671102, 504779781, 494121004, 483689711]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1252).prefactor = (2865997940217569/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1252).cutoff/(generalMeanRows 1252).c)).2 =
    (189408945892039/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1252).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1252).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1252).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1252

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1252).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1252).criticalRate j.val*(generalMeanRows 1252).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1252).c*(generalMeanRows 1252).criticalPoint j.val)).2-
      (generalMeanRows 1252).J/2-(generalMeanRows 1252).error (generalMeanGrid j.val)+
      (generalMeanRows 1252).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1252).c)).2-
      (generalMeanRows 1252).J/2-(generalMeanRows 1252).error 4 := by
  have he : (generalMeanRows 1252).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1252) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1252)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1252

/-! Kernel-checked entropy margins for general spectral rectangle 1253. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1253
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7684429600, 7503422552, 7328158596, 7158338137, 6993686291, 6833950230, 6678896861, 6528310787, 6381992506, 6239756834, 6101431508, 5966855948, 5835880162, 5708363773, 5584175153, 5463190650, 5345293902, 5230375219, 5118331031, 5009063392, 4902479536, 4798491475, 4697015636, 4597972536, 4501286483, 4406885312, 4314700136, 4224665129, 4136717319, 4050796408, 3966844601, 3884806450, 3804628716, 3726260237, 3649651806, 3574756064, 3501527397, 3429921840, 3359896992, 3291411934, 3224427153, 3158904476, 3094806999, 3032099031, 2970746036, 2910714579, 2851972278, 2794487755, 2738230598, 2683171311, 2629281285, 2576532755, 2524898768, 2474353152, 2424870483, 2376426057, 2328995865, 2282556562, 2237085449, 2192560442, 2148960057, 2106263386, 2064450075, 2023500307, 1983394786, 1944114713, 1905641777, 1867958133, 1831046393, 1794889604, 1759471241, 1724775189, 1690785734, 1657487546, 1624865674, 1592905528, 1561592871, 1530913810, 1500854786, 1471402559, 1442544206, 1414267108, 1386558942, 1359407675, 1332801550, 1306729087, 1281179067, 1256140532, 1231602772, 1207555324, 1183987959, 1160890683, 1138253725, 1116067535, 1094322777, 1073010320, 1052121241, 1031646811, 1011578497, 991907950, 972627009, 953727689, 935202180, 917042842, 899242202, 881792948, 864687926, 847920137, 831482732, 815369009, 799572411, 784086518, 768905049, 754021856, 739430923, 725126359, 711102399, 697353399, 683873835, 670658298, 657701492]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1253).prefactor = (5798005218643371/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1253).cutoff/(generalMeanRows 1253).c)).2 =
    (973304444043751/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1253).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1253).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1253).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1253

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1253).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1253).criticalRate j.val*(generalMeanRows 1253).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1253).c*(generalMeanRows 1253).criticalPoint j.val)).2-
      (generalMeanRows 1253).J/2-(generalMeanRows 1253).error (generalMeanGrid j.val)+
      (generalMeanRows 1253).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1253).c)).2-
      (generalMeanRows 1253).J/2-(generalMeanRows 1253).error 4 := by
  have he : (generalMeanRows 1253).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1253) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1253)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1253

/-! Kernel-checked entropy margins for general spectral rectangle 1254. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1254
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5384005939, 5230963865, 5083197825, 4940446838, 4802469872, 4669043740, 4539961263, 4415029668, 4294069173, 4176911748, 4063400017, 3953386295, 3846731726, 3743305525, 3642984294, 3545651423, 3451196545, 3359515051, 3270507655, 3184080000, 3100142305, 3018609043, 2939398651, 2862433266, 2787638487, 2714943151, 2644279137, 2575581181, 2508786707, 2443835674, 2380670431, 2319235588, 2259477892, 2201346116, 2144790954, 2089764923, 2036222273, 1984118905, 1933412289, 1884061391, 1836026607, 1789269696, 1743753717, 1699442978, 1656302978, 1614300359, 1573402854, 1533579247, 1494799330, 1457033857, 1420254514, 1384433877, 1349545380, 1315563282, 1282462635, 1250219258, 1218809703, 1188211234, 1158401799, 1129360006, 1101065098, 1073496933, 1046635963, 1020463213, 994960259, 970109215, 945892708, 922293869, 899296309, 876884107, 855041796, 833754346, 813007151, 792786013, 773077136, 753867106, 735142882, 716891786, 699101490, 681760004, 664855670, 648377147, 632313406, 616653716, 601387640, 586505023, 571995983, 557850908, 544060441, 530615478, 517507159, 504726862, 492266191, 480116977, 468271268, 456721322, 445459600, 434478766, 423771675, 413331370, 403151079, 393224204, 383544323, 374105182, 364900687, 355924908, 347172064, 338636529, 330312819, 322195597, 314279659, 306559938, 299031500, 291689535, 284529358, 277546404, 270736229, 264094497, 257616988, 251299590, 245138292]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1254).prefactor = (5000986074573863/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1254).cutoff/(generalMeanRows 1254).c)).2 =
    (995978892477881/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1254).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1254).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1254).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1254

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1254).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1254).criticalRate j.val*(generalMeanRows 1254).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1254).c*(generalMeanRows 1254).criticalPoint j.val)).2-
      (generalMeanRows 1254).J/2-(generalMeanRows 1254).error (generalMeanGrid j.val)+
      (generalMeanRows 1254).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1254).c)).2-
      (generalMeanRows 1254).J/2-(generalMeanRows 1254).error 4 := by
  have he : (generalMeanRows 1254).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1254) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1254)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1254

/-! Kernel-checked entropy margins for general spectral rectangle 1255. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1255
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6530095821, 6343738589, 6163949373, 5990389536, 5822747055, 5660733738, 5504082776, 5352546603, 5205894998, 5063913421, 4926401530, 4793171877, 4664048745, 4538867108, 4417471716, 4299716268, 4185462675, 4074580397, 3966945856, 3862441893, 3760957294, 3662386350, 3566628466, 3473587803, 3383172955, 3295296652, 3209875494, 3126829702, 3046082899, 2967561898, 2891196517, 2816919404, 2744665878, 2674373782, 2605983341, 2539437046, 2474679525, 2411657446, 2350319404, 2290615839, 2232498937, 2175922556, 2120842143, 2067214668, 2014998552, 1964153605, 1914640967, 1866423050, 1819463487, 1773727081, 1729179759, 1685788525, 1643521420, 1602347479, 1562236698, 1523159992, 1485089165, 1447996875, 1411856603, 1376642626, 1342329984, 1308894459, 1276312542, 1244561416, 1213618926, 1183463562, 1154074432, 1125431247, 1097514294, 1070304425, 1043783035, 1017932041, 992733871, 968171447, 944228165, 920887884, 898134912, 875953988, 854330275, 833249339, 812697145, 792660040, 773124743, 754078331, 735508235, 717402223, 699748392, 682535161, 665751257, 649385710, 633427843, 617867262, 602693851, 587897759, 573469399, 559399435, 545678779, 532298581, 519250222, 506525312, 494115677, 482013360, 470210610, 458699878, 447473809, 436525244, 425847204, 415432895, 405275697, 395369160, 385707001, 376283100, 367091492, 358126367, 349382064, 340853066, 332533997, 324419621, 316504832, 308784657, 301254248]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1255).prefactor = (3069815452329029/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1255).cutoff/(generalMeanRows 1255).c)).2 =
    (900622892608943/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1255).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1255).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1255).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1255

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1255).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1255).criticalRate j.val*(generalMeanRows 1255).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1255).c*(generalMeanRows 1255).criticalPoint j.val)).2-
      (generalMeanRows 1255).J/2-(generalMeanRows 1255).error (generalMeanGrid j.val)+
      (generalMeanRows 1255).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1255).c)).2-
      (generalMeanRows 1255).J/2-(generalMeanRows 1255).error 4 := by
  have he : (generalMeanRows 1255).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1255) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1255)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1255

/-! Kernel-checked entropy margins for general spectral rectangle 1256. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1256
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6268865832, 6120965473, 5977658332, 5838714692, 5703923335, 5573089540, 5446033339, 5322587983, 5202598605, 5085921046, 4972420811, 4861972159, 4754457292, 4649765635, 4547793202, 4448442023, 4351619645, 4257238671, 4165216358, 4075474255, 3987937871, 3902536381, 3819202361, 3737871543, 3658482599, 3580976942, 3505298543, 3431393766, 3359211218, 3288701611, 3219817636, 3152513843, 3086746537, 3022473679, 2959654794, 2898250889, 2838224369, 2779538971, 2722159694, 2666052737, 2611185437, 2557526221, 2505044550, 2453710874, 2403496586, 2354373981, 2306316214, 2259297270, 2213291920, 2168275697, 2124224858, 2081116359, 2038927827, 1997637532, 1957224363, 1917667808, 1878947927, 1841045331, 1803941168, 1767617097, 1732055272, 1697238328, 1663149360, 1629771909, 1597089949, 1565087870, 1533750464, 1503062915, 1473010784, 1443579998, 1414756837, 1386527925, 1358880220, 1331800999, 1305277854, 1279298681, 1253851670, 1228925295, 1204508309, 1180589735, 1157158855, 1134205209, 1111718582, 1089688999, 1068106719, 1046962229, 1026246236, 1005949661, 986063637, 966579499, 947488779, 928783204, 910454687, 892495327, 874897398, 857653349, 840755798, 824197530, 807971487, 792070772, 776488636, 761218484, 746253862, 731588461, 717216108, 703130767, 689326532, 675797626, 662538398, 649543318, 636806975, 624324078, 612089447, 600098013, 588344816, 576825004, 565533826, 554466633, 543618876, 532986100, 522563946]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1256).prefactor = (4690968656925781/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1256).cutoff/(generalMeanRows 1256).c)).2 =
    (1052805293129117/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1256).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1256).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1256).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1256

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1256).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1256).criticalRate j.val*(generalMeanRows 1256).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1256).c*(generalMeanRows 1256).criticalPoint j.val)).2-
      (generalMeanRows 1256).J/2-(generalMeanRows 1256).error (generalMeanGrid j.val)+
      (generalMeanRows 1256).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1256).c)).2-
      (generalMeanRows 1256).J/2-(generalMeanRows 1256).error 4 := by
  have he : (generalMeanRows 1256).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1256) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1256)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1256

/-! Kernel-checked entropy margins for general spectral rectangle 1257. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1257
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4619075363, 4485090027, 4355788692, 4230938853, 4110325712, 3993750318, 3881027945, 3771986671, 3666466129, 3564316406, 3465397076, 3369576342, 3276730272, 3186742127, 3099501757, 3014905063, 2932853517, 2853253731, 2776017069, 2701059297, 2628300269, 2557663641, 2489076610, 2422469686, 2357776468, 2294933459, 2233879879, 2174557507, 2116910526, 2060885390, 2006430695, 1953497058, 1902037013, 1852004909, 1803356814, 1756050434, 1710045024, 1665301320, 1621781466, 1579448945, 1538268525, 1498206191, 1459229101, 1421305526, 1384404810, 1348497317, 1313554394, 1279548328, 1246452311, 1214240396, 1182887473, 1152369230, 1122662123, 1093743348, 1065590812, 1038183110, 1011499493, 985519849, 960224682, 935595082, 911612713, 888259788, 865519050, 843373755, 821807656, 800804982, 780350425, 760429126, 741026654, 722129000, 703722556, 685794109, 668330820, 651320220, 634750193, 618608967, 602885104, 587567487, 572645311, 558108076, 543945573, 530147878, 516705345, 503608592, 490848500, 478416199, 466303063, 454500705, 443000967, 431795912, 420877824, 410239191, 399872711, 389771277, 379927975, 370336078, 360989039, 351880489, 343004231, 334354232, 325924623, 317709689, 309703870, 301901754, 294298073, 286887699, 279665640, 272627037, 265767159, 259081401, 252565278, 246214426, 240024594, 233991643, 228111544, 222380374, 216794311, 211349635, 206042723, 200870047, 195828169]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1257).prefactor = (4399933295595671/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1257).cutoff/(generalMeanRows 1257).c)).2 =
    (980829253011753/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1257).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1257).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1257).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1257

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1257).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1257).criticalRate j.val*(generalMeanRows 1257).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1257).c*(generalMeanRows 1257).criticalPoint j.val)).2-
      (generalMeanRows 1257).J/2-(generalMeanRows 1257).error (generalMeanGrid j.val)+
      (generalMeanRows 1257).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1257).c)).2-
      (generalMeanRows 1257).J/2-(generalMeanRows 1257).error 4 := by
  have he : (generalMeanRows 1257).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1257) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1257)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1257

/-! Kernel-checked entropy margins for general spectral rectangle 1258. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1258
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4814048455, 4677153825, 4544984315, 4417305689, 4293901641, 4174571904, 4059130604, 3947404812, 3839233280, 3734465321, 3632959827, 3534584399, 3439214571, 3346733131, 3257029505, 3169999215, 3085543391, 3003568335, 2923985127, 2846709272, 2771660384, 2698761892, 2627940783, 2559127364, 2492255045, 2427260141, 2364081695, 2302661308, 2242942993, 2184873034, 2128399857, 2073473911, 2020047561, 1968074987, 1917512087, 1868316395, 1820446992, 1773864440, 1728530705, 1684409090, 1641464180, 1599661778, 1558968852, 1519353485, 1480784829, 1443233055, 1406669311, 1371065688, 1336395173, 1302631619, 1269749709, 1237724924, 1206533510, 1176152454, 1146559450, 1117732877, 1089651773, 1062295809, 1035645270, 1009681029, 984384529, 959737763, 935723252, 912324032, 889523632, 867306059, 845655784, 824557723, 803997224, 783960054, 764432384, 745400776, 726852173, 708773881, 691153566, 673979235, 657239229, 640922214, 625017167, 609513370, 594400400, 579668118, 565306663, 551306442, 537658123, 524352628, 511381122, 498735011, 486405930, 474385740, 462666520, 451240560, 440100356, 429238604, 418648194, 408322204, 398253896, 388436710, 378864257, 369530320, 360428841, 351553925, 342899829, 334460961, 326231874, 318207265, 310381967, 302750949, 295309310, 288052275, 280975195, 274073540, 267342896, 260778965, 254377557, 248134593, 242046097, 236108195, 230317113, 224669174, 219160794]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1258).prefactor = (2235513818331677/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1258).cutoff/(generalMeanRows 1258).c)).2 =
    (988861424709019/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1258).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1258).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1258).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1258

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1258).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1258).criticalRate j.val*(generalMeanRows 1258).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1258).c*(generalMeanRows 1258).criticalPoint j.val)).2-
      (generalMeanRows 1258).J/2-(generalMeanRows 1258).error (generalMeanGrid j.val)+
      (generalMeanRows 1258).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1258).c)).2-
      (generalMeanRows 1258).J/2-(generalMeanRows 1258).error 4 := by
  have he : (generalMeanRows 1258).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1258) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1258)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1258

/-! Kernel-checked entropy margins for general spectral rectangle 1259. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1259
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4538377481, 4410970558, 4287860526, 4168842706, 4053727501, 3942338825, 3834512731, 3730096219, 3628946180, 3530928482, 3435917150, 3343793651, 3254446252, 3167769458, 3083663506, 3002033909, 2922791056, 2845849845, 2771129359, 2698552565, 2628046050, 2559539776, 2492966861, 2428263375, 2365368157, 2304222646, 2244770728, 2186958591, 2130734597, 2076049161, 2022854634, 1971105210, 1920756818, 1871767042, 1824095035, 1777701441, 1732548324, 1688599098, 1645818469, 1604172369, 1563627909, 1524153318, 1485717899, 1448291984, 1411846884, 1376354857, 1341789061, 1308123521, 1275333095, 1243393439, 1212280976, 1181972868, 1152446986, 1123681884, 1095656775, 1068351504, 1041746525, 1015822883, 990562187, 965946595, 941958792, 918581974, 895799827, 873596512, 851956652, 830865311, 810307983, 790270576, 770739400, 751701154, 733142912, 715052110, 697416539, 680224328, 663463939, 647124153, 631194060, 615663051, 600520809, 585757300, 571362762, 557327699, 543642874, 530299299, 517288229, 504601154, 492229793, 480166087, 468402190, 456930470, 445743492, 434834024, 424195022, 413819630, 403701171, 393833145, 384209223, 374823241, 365669198, 356741248, 348033699, 339541006, 331257770, 323178728, 315298759, 307612871, 300116202, 292804015, 285671695, 278714747, 271928790, 265309556, 258852886, 252554730, 246411137, 240418260, 234572350, 228869754, 223306909, 217880345, 212586680]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1259).prefactor = (255844154932599/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1259).cutoff/(generalMeanRows 1259).c)).2 =
    (68583946722501/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1259).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1259).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1259).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1259

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1259).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1259).criticalRate j.val*(generalMeanRows 1259).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1259).c*(generalMeanRows 1259).criticalPoint j.val)).2-
      (generalMeanRows 1259).J/2-(generalMeanRows 1259).error (generalMeanGrid j.val)+
      (generalMeanRows 1259).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1259).c)).2-
      (generalMeanRows 1259).J/2-(generalMeanRows 1259).error 4 := by
  have he : (generalMeanRows 1259).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1259) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1259)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1259

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock17 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 17 i) := by
  fin_cases i
  · exact EntropyRow1190.numerical
  · exact EntropyRow1191.numerical
  · exact EntropyRow1192.numerical
  · exact EntropyRow1193.numerical
  · exact EntropyRow1194.numerical
  · exact EntropyRow1195.numerical
  · exact EntropyRow1196.numerical
  · exact EntropyRow1197.numerical
  · exact EntropyRow1198.numerical
  · exact EntropyRow1199.numerical
  · exact EntropyRow1200.numerical
  · exact EntropyRow1201.numerical
  · exact EntropyRow1202.numerical
  · exact EntropyRow1203.numerical
  · exact EntropyRow1204.numerical
  · exact EntropyRow1205.numerical
  · exact EntropyRow1206.numerical
  · exact EntropyRow1207.numerical
  · exact EntropyRow1208.numerical
  · exact EntropyRow1209.numerical
  · exact EntropyRow1210.numerical
  · exact EntropyRow1211.numerical
  · exact EntropyRow1212.numerical
  · exact EntropyRow1213.numerical
  · exact EntropyRow1214.numerical
  · exact EntropyRow1215.numerical
  · exact EntropyRow1216.numerical
  · exact EntropyRow1217.numerical
  · exact EntropyRow1218.numerical
  · exact EntropyRow1219.numerical
  · exact EntropyRow1220.numerical
  · exact EntropyRow1221.numerical
  · exact EntropyRow1222.numerical
  · exact EntropyRow1223.numerical
  · exact EntropyRow1224.numerical
  · exact EntropyRow1225.numerical
  · exact EntropyRow1226.numerical
  · exact EntropyRow1227.numerical
  · exact EntropyRow1228.numerical
  · exact EntropyRow1229.numerical
  · exact EntropyRow1230.numerical
  · exact EntropyRow1231.numerical
  · exact EntropyRow1232.numerical
  · exact EntropyRow1233.numerical
  · exact EntropyRow1234.numerical
  · exact EntropyRow1235.numerical
  · exact EntropyRow1236.numerical
  · exact EntropyRow1237.numerical
  · exact EntropyRow1238.numerical
  · exact EntropyRow1239.numerical
  · exact EntropyRow1240.numerical
  · exact EntropyRow1241.numerical
  · exact EntropyRow1242.numerical
  · exact EntropyRow1243.numerical
  · exact EntropyRow1244.numerical
  · exact EntropyRow1245.numerical
  · exact EntropyRow1246.numerical
  · exact EntropyRow1247.numerical
  · exact EntropyRow1248.numerical
  · exact EntropyRow1249.numerical
  · exact EntropyRow1250.numerical
  · exact EntropyRow1251.numerical
  · exact EntropyRow1252.numerical
  · exact EntropyRow1253.numerical
  · exact EntropyRow1254.numerical
  · exact EntropyRow1255.numerical
  · exact EntropyRow1256.numerical
  · exact EntropyRow1257.numerical
  · exact EntropyRow1258.numerical
  · exact EntropyRow1259.numerical
end SingularValueBounds.KL.Certificates
