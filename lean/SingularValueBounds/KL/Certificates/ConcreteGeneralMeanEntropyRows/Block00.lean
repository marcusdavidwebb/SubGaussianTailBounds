import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 0. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0000
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8851862756, 8551147021, 8265148066, 7992981596, 7733826739, 7486920466, 7251552617, 7027061464, 6812829726, 6608280999, 6412876525, 6226112288, 6047516367, 5876646548, 5713088136, 5556451973, 5406372618, 5262506686, 5124531320, 4992142796, 4865055228, 4742999385, 4625721593, 4512982727, 4404557271, 4300232453, 4199807442, 4103092601, 4009908794, 3920086742, 3833466424, 3749896516, 3669233875, 3591343044, 3516095806, 3443370759, 3373052913, 3305033326, 3239208752, 3175481319, 3113758219, 3053951427, 2995977428, 2939756966, 2885214811, 2832279531, 2780883284, 2730961625, 2682453315, 2635300153, 2589446805, 2544840657, 2501431663, 2459172211, 2418016993, 2377922884, 2338848822, 2300755708, 2263606296, 2227365099, 2191998297, 2157473652, 2123760424, 2090829297, 2058652302, 2027202754, 1996455179, 1966385259, 1936969771, 1908186531, 1880014345, 1852432956, 1825422997, 1798965951, 1773044104, 1747640508, 1722738945, 1698323885, 1674380459, 1650894423, 1627852130, 1605240498, 1583046986, 1561259565, 1539866697, 1518857309, 1498220771, 1477946875, 1458025816, 1438448174, 1419204893, 1400287266, 1381686918, 1363395793, 1345406134, 1327710476, 1310301626, 1293172657, 1276316891, 1259727889, 1243399442, 1227325559, 1211500458, 1195918557, 1180574464, 1165462969, 1150579037, 1135917801, 1121474551, 1107244733, 1093223937, 1079407893, 1065792466, 1052373649, 1039147559, 1026110430, 1013258609, 1000588552, 988096820, 975780072, 963635065]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 0).prefactor = (7333378285055737/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 0).cutoff/(generalMeanRows 0).c)).2 =
    (1920215860397/4000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 0).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 0).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 0).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 0

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 0).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 0).criticalRate j.val*(generalMeanRows 0).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 0).c*(generalMeanRows 0).criticalPoint j.val)).2-
      (generalMeanRows 0).J/2-(generalMeanRows 0).error (generalMeanGrid j.val)+
      (generalMeanRows 0).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 0).c)).2-
      (generalMeanRows 0).J/2-(generalMeanRows 0).error 4 := by
  have he : (generalMeanRows 0).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 0) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 0)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0000

/-! Kernel-checked entropy margins for general spectral rectangle 1. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0001
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8027293837, 7715300791, 7418739642, 7136689407, 6868295171, 6612762244, 6369350969, 6137372074, 5916182523, 5705181778, 5503808437, 5311537193, 5127876087, 4952364008, 4784568423, 4624083307, 4470527249, 4323541730, 4182789527, 4047953264, 3918734072, 3794850354, 3676036651, 3562042589, 3452631908, 3347581567, 3246680906, 3149730877, 3056543323, 2966940314, 2880753521, 2797823645, 2717999870, 2641139365, 2567106813, 2495773974, 2427019271, 2360727409, 2296789016, 2235100307, 2175562767, 2118082854, 2062571725, 2008944976, 1957122391, 1907027721, 1858588460, 1811735646, 1766403671, 1722530096, 1680055487, 1638923251, 1599079489, 1560472851, 1523054405, 1486777510, 1451597697, 1417472555, 1384361628, 1352226312, 1321029763, 1290736807, 1261313852, 1232728813, 1204951035, 1177951219, 1151701359, 1126174673, 1101345546, 1077189471, 1053682998, 1030803676, 1008530011, 986841416, 965718169, 945141370, 925092905, 905555403, 886512207, 867947336, 849845455, 832191845, 814972373, 798173468, 781782089, 765785709, 750172284, 734930235, 720048426, 705516144, 691323079, 677459308, 663915278, 650681786, 637749968, 625111282, 612757492, 600680661, 588873130, 577327512, 566036678, 554993748, 544192078, 533625250, 523287064, 513171532, 503272861, 493585453, 484103893, 474822943, 465737534, 456842759, 448133868, 439606261, 431255483, 423077214, 415067271, 407221596, 399536256, 392007436, 384631433]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1).prefactor = (1937292430772137/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1).cutoff/(generalMeanRows 1).c)).2 =
    (192694369279087/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1).criticalRate j.val*(generalMeanRows 1).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1).c*(generalMeanRows 1).criticalPoint j.val)).2-
      (generalMeanRows 1).J/2-(generalMeanRows 1).error (generalMeanGrid j.val)+
      (generalMeanRows 1).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1).c)).2-
      (generalMeanRows 1).J/2-(generalMeanRows 1).error 4 := by
  have he : (generalMeanRows 1).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0001

/-! Kernel-checked entropy margins for general spectral rectangle 2. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0002
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6982729328, 6670193439, 6373726987, 6092368274, 5825224549, 5571465888, 5330319770, 5101066218, 4883033463, 4675594038, 4478161271, 4290186110, 4111154255, 3940583553, 3778021632, 3623043737, 3475250769, 3334267477, 3199740808, 3071338392, 2948747150, 2831672008, 2719834718, 2612972762, 2510838347, 2413197466, 2319829036, 2230524091, 2145085039, 2063324969, 1985067001, 1910143692, 1838396469, 1769675113, 1703837266, 1640747976, 1580279274, 1522309773, 1466724295, 1413413519, 1362273657, 1313206145, 1266117354, 1220918319, 1177524483, 1135855462, 1095834815, 1057389837, 1020451355, 984953545, 950833749, 918032318, 886492445, 856160023, 826983504, 798913767, 771903992, 745909545, 720887865, 696798361, 673602310, 651262767, 629744472, 609013770, 589038530, 569788068, 551233078, 533345567, 516098784, 499467168, 483426283, 467952770, 453024291, 438619483, 424717909, 411300018, 398347099, 385841243, 373765306, 362102875, 350838228, 339956310, 329442696, 319283564, 309465668, 299976312, 290803324, 281935032, 273360241, 265068216, 257048655, 249291672, 241787783, 234527880, 227503222, 220705413, 214126391, 207758413, 201594037, 195626116, 189847778, 184252419, 178833690, 173585487, 168501937, 163577394, 158806426, 154183805, 149704501, 145363672, 141156659, 137078974, 133126296, 129294464, 125579469, 121977449, 118484685, 115097589, 111812707, 108626705, 105536372]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 2).prefactor = (4094267952848139/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 2).cutoff/(generalMeanRows 2).c)).2 =
    (132013940776953/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 2).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 2).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 2).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 2

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 2).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 2).criticalRate j.val*(generalMeanRows 2).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 2).c*(generalMeanRows 2).criticalPoint j.val)).2-
      (generalMeanRows 2).J/2-(generalMeanRows 2).error (generalMeanGrid j.val)+
      (generalMeanRows 2).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 2).c)).2-
      (generalMeanRows 2).J/2-(generalMeanRows 2).error 4 := by
  have he : (generalMeanRows 2).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 2) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 2)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0002

/-! Kernel-checked entropy margins for general spectral rectangle 3. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0003
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6491572586, 6283423401, 6085717817, 5897795475, 5719044809, 5548898783, 5386831074, 5232352650, 5085008694, 4944375837, 4810059646, 4681692358, 4558930823, 4441454626, 4328964384, 4221180186, 4117840167, 4018699204, 3923527722, 3832110588, 3744246104, 3659745077, 3578429956, 3500134043, 3424700761, 3351982975, 3281842366, 3214148852, 3148780046, 3085620760, 3024562538, 2965503227, 2908346574, 2853001854, 2799383521, 2747410887, 2697007814, 2648102440, 2600626912, 2554517138, 2509712566, 2466155959, 2423793205, 2382573122, 2342447286, 2303369868, 2265297478, 2228189022, 2192005566, 2156710214, 2122267982, 2088645695, 2055811877, 2023736655, 1992391666, 1961749975, 1931785988, 1902475380, 1873795023, 1845722915, 1818238124, 1791320722, 1764951732, 1739113075, 1713787522, 1688958645, 1664610774, 1640728957, 1617298920, 1594307030, 1571740263, 1549586167, 1527832837, 1506468883, 1485483401, 1464865952, 1444606535, 1424695564, 1405123848, 1385882568, 1366963263, 1348357806, 1330058390, 1312057513, 1294347960, 1276922791, 1259775325, 1242899130, 1226288008, 1209935988, 1193837308, 1177986412, 1162377937, 1147006703, 1131867706, 1116956110, 1102267238, 1087796566, 1073539712, 1059492438, 1045650634, 1032010319, 1018567632, 1005318827, 992260271, 979388434, 966699889, 954191306, 941859449, 929701167, 917713400, 905893166, 894237564, 882743766, 871409020, 860230641, 849206013, 838332582, 827607858, 817029410, 806594866]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 3).prefactor = (2898898535834433/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 3).cutoff/(generalMeanRows 3).c)).2 =
    (539969618435087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 3).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 3).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 3).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 3

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 3).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 3).criticalRate j.val*(generalMeanRows 3).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 3).c*(generalMeanRows 3).criticalPoint j.val)).2-
      (generalMeanRows 3).J/2-(generalMeanRows 3).error (generalMeanGrid j.val)+
      (generalMeanRows 3).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 3).c)).2-
      (generalMeanRows 3).J/2-(generalMeanRows 3).error 4 := by
  have he : (generalMeanRows 3).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 3) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 3)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0003

/-! Kernel-checked entropy margins for general spectral rectangle 4. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0004
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6731555493, 6515711370, 6310696932, 6115827405, 5930468617, 5754032569, 5585973480, 5425784239, 5272993216, 5127161391, 4987879747, 4854766929, 4727467099, 4605647998, 4488999174, 4377230369, 4270070037, 4167263995, 4068574177, 3973777500, 3882664809, 3795039915, 3710718706, 3629528320, 3551306392, 3475900347, 3403166754, 3332970720, 3265185336, 3199691153, 3136375708, 3075133070, 3015863429, 2958472704, 2902872189, 2848978210, 2796711817, 2745998491, 2696767870, 2648953493, 2602492568, 2557325744, 2513396908, 2470652985, 2429043762, 2388521716, 2349041851, 2310561555, 2273040456, 2236440291, 2200724786, 2165859538, 2131811907, 2098550916, 2066047154, 2034272689, 2003200982, 1972806809, 1943066185, 1913956297, 1885455438, 1857542943, 1830199134, 1803405264, 1777143467, 1751396706, 1726148734, 1701384045, 1677087837, 1653245975, 1629844950, 1606871854, 1584314339, 1562160593, 1540399312, 1519019670, 1498011295, 1477364248, 1457068997, 1437116398, 1417497677, 1398204406, 1379228491, 1360562151, 1342197904, 1324128555, 1306347175, 1288847094, 1271621887, 1254665358, 1237971536, 1221534659, 1205349163, 1189409680, 1173711019, 1158248166, 1143016270, 1128010640, 1113226734, 1098660155, 1084306642, 1070162066, 1056222425, 1042483833, 1028942523, 1015594835, 1002437216, 989466211, 976678464, 964070711, 951639776, 939382567, 927296076, 915377371, 903623598, 892031972, 880599781, 869324377, 858203178, 847233662, 836413370]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 4).prefactor = (6012132223762353/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 4).cutoff/(generalMeanRows 4).c)).2 =
    (539969618435087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 4).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 4).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 4).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 4

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 4).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 4).criticalRate j.val*(generalMeanRows 4).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 4).c*(generalMeanRows 4).criticalPoint j.val)).2-
      (generalMeanRows 4).J/2-(generalMeanRows 4).error (generalMeanGrid j.val)+
      (generalMeanRows 4).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 4).c)).2-
      (generalMeanRows 4).J/2-(generalMeanRows 4).error 4 := by
  have he : (generalMeanRows 4).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 4) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 4)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0004

/-! Kernel-checked entropy margins for general spectral rectangle 5. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0005
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6823972305, 6600194454, 6387644299, 6185613267, 5993445131, 5810531429, 5636307372, 5470248168, 5311865725, 5160705678, 5016344695, 4878388051, 4746467411, 4620238823, 4499380890, 4383593093, 4272594267, 4166121200, 4063927347, 3965781654, 3871467473, 3780781561, 3693533162, 3609543156, 3528643277, 3450675383, 3375490785, 3302949628, 3232920308, 3165278942, 3099908868, 3036700181, 2975549306, 2916358597, 2859035962, 2803494522, 2749652278, 2697431819, 2646760033, 2597567849, 2549789987, 2503364731, 2458233716, 2414341721, 2371636490, 2330068548, 2289591042, 2250159581, 2211732100, 2174268716, 2137731605, 2102084884, 2067294496, 2033328108, 2000155011, 1967746027, 1936073425, 1905110835, 1874833177, 1845216583, 1816238333, 1787876791, 1760111345, 1732922348, 1706291069, 1680199641, 1654631015, 1629568912, 1604997789, 1580902791, 1557269721, 1534085001, 1511335641, 1489009208, 1467093796, 1445578000, 1424450888, 1403701977, 1383321212, 1363298942, 1343625900, 1324293185, 1305292241, 1286614842, 1268253074, 1250199320, 1232446248, 1214986793, 1197814146, 1180921743, 1164303250, 1147952555, 1131863758, 1116031158, 1100449244, 1085112690, 1070016345, 1055155220, 1040524488, 1026119475, 1011935647, 997968614, 984214114, 970668016, 957326306, 944185090, 931240582, 918489106, 905927086, 893551045, 881357600, 869343458, 857505412, 845840341, 834345202, 823017029, 811852931, 800850088, 790005749, 779317229, 768781906]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 5).prefactor = (3117195499358631/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 5).cutoff/(generalMeanRows 5).c)).2 =
    (131998356847093/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 5).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 5).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 5).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 5

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 5).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 5).criticalRate j.val*(generalMeanRows 5).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 5).c*(generalMeanRows 5).criticalPoint j.val)).2-
      (generalMeanRows 5).J/2-(generalMeanRows 5).error (generalMeanGrid j.val)+
      (generalMeanRows 5).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 5).c)).2-
      (generalMeanRows 5).J/2-(generalMeanRows 5).error 4 := by
  have he : (generalMeanRows 5).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 5) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 5)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0005

/-! Kernel-checked entropy margins for general spectral rectangle 6. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0006
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6919048990, 6687159855, 6466911413, 6257570368, 6058457583, 5868943333, 5688443075, 5516413641, 5352349828, 5195781317, 5046269892, 4903406921, 4766811071, 4636126228, 4511019602, 4391180000, 4276316243, 4166155719, 4060443054, 3958938896, 3861418787, 3767672139, 3677501274, 3590720550, 3507155549, 3426642324, 3349026708, 3274163668, 3201916707, 3132157314, 3064764446, 2999624054, 2936628633, 2875676814, 2816672976, 2759526887, 2704153371, 2650471995, 2598406778, 2547885919, 2498841543, 2451209464, 2404928964, 2359942583, 2316195928, 2273637490, 2232218470, 2191892627, 2152616123, 2114347384, 2077046971, 2040677454, 2005203298, 1970590755, 1936807760, 1903823837, 1871610011, 1840138720, 1809383738, 1779320100, 1749924033, 1721172888, 1693045079, 1665520025, 1638578097, 1612200561, 1586369536, 1561067944, 1536279467, 1511988508, 1488180153, 1464840134, 1441954792, 1419511053, 1397496389, 1375898796, 1354706763, 1333909248, 1313495655, 1293455810, 1273779942, 1254458660, 1235482935, 1216844082, 1198533745, 1180543879, 1162866733, 1145494840, 1128421002, 1111638274, 1095139957, 1078919583, 1062970904, 1047287885, 1031864692, 1016695681, 1001775394, 987098546, 972660022, 958454863, 944478267, 930725576, 917192272, 903873972, 890766420, 877865485, 865167153, 852667521, 840362798, 828249294, 816323421, 804581685, 793020686, 781637112, 770427735, 759389412, 748519076, 737813737, 727270479, 716886456, 706658889]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 6).prefactor = (1616216580004111/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 6).cutoff/(generalMeanRows 6).c)).2 =
    (64519871217671/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 6).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 6).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 6).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 6

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 6).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 6).criticalRate j.val*(generalMeanRows 6).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 6).c*(generalMeanRows 6).criticalPoint j.val)).2-
      (generalMeanRows 6).J/2-(generalMeanRows 6).error (generalMeanGrid j.val)+
      (generalMeanRows 6).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 6).c)).2-
      (generalMeanRows 6).J/2-(generalMeanRows 6).error 4 := by
  have he : (generalMeanRows 6).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 6) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 6)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0006

/-! Kernel-checked entropy margins for general spectral rectangle 7. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0007
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6863749776, 6623948860, 6396215053, 6179790712, 5973974113, 5778114546, 5591607941, 5413892940, 5244447369, 5082785060, 4928452977, 4781028615, 4640117643, 4505351751, 4376386700, 4252900536, 4134591956, 4021178816, 3912396762, 3807997968, 3707749982, 3611434661, 3518847185, 3429795158, 3344097764, 3261584996, 3182096940, 3105483112, 3031601839, 2960319692, 2891510955, 2825057131, 2760846484, 2698773615, 2638739061, 2580648929, 2524414549, 2469952152, 2417182572, 2366030964, 2316426544, 2268302343, 2221594977, 2176244436, 2132193884, 2089389467, 2047780143, 2007317515, 1967955679, 1929651074, 1892362354, 1856050257, 1820677486, 1786208598, 1752609900, 1719849346, 1687896451, 1656722198, 1626298960, 1596600421, 1567601506, 1539278308, 1511608033, 1484568930, 1458140239, 1432302140, 1407035698, 1382322819, 1358146202, 1334489303, 1311336288, 1288672003, 1266481931, 1244752168, 1223469383, 1202620794, 1182194139, 1162177647, 1142560019, 1123330398, 1104478351, 1085993846, 1067867236, 1050089235, 1032650904, 1015543634, 998759128, 982289389, 966126705, 950263635, 934692995, 919407850, 904401500, 889667469, 875199497, 860991528, 847037702, 833332346, 819869967, 806645244, 793653018, 780888288, 768346205, 756022062, 743911291, 732009458, 720312253, 708815491, 697515102, 686407131, 675487730, 664753154, 654199759, 643823998, 633622416, 623591646, 613728408, 604029507, 594491824, 585112319, 575888027]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 7).prefactor = (837982742506089/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 7).cutoff/(generalMeanRows 7).c)).2 =
    (4929021075771/10000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 7).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 7).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 7).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 7

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 7).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 7).criticalRate j.val*(generalMeanRows 7).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 7).c*(generalMeanRows 7).criticalPoint j.val)).2-
      (generalMeanRows 7).J/2-(generalMeanRows 7).error (generalMeanGrid j.val)+
      (generalMeanRows 7).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 7).c)).2-
      (generalMeanRows 7).J/2-(generalMeanRows 7).error 4 := by
  have he : (generalMeanRows 7).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 7) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 7)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0007

/-! Kernel-checked entropy margins for general spectral rectangle 8. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0008
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6261488577, 6017108400, 5785221446, 5565048564, 5355867949, 5157010112, 4967853380, 4787819866, 4616371849, 4453008514, 4297263000, 4148699736, 4006912022, 3871519828, 3742167787, 3618523373, 3500275225, 3387131620, 3278819069, 3175081028, 3075676718, 2980380033, 2888978535, 2801272527, 2717074200, 2636206839, 2558504092, 2483809290, 2411974822, 2342861546, 2276338250, 2212281152, 2150573425, 2091104765, 2033770986, 1978473641, 1925119667, 1873621063, 1823894576, 1775861419, 1729447002, 1684580680, 1641195524, 1599228097, 1558618252, 1519308941, 1481246032, 1444378143, 1408656486, 1374034714, 1340468788, 1307916843, 1276339066, 1245697583, 1215956351, 1187081054, 1159039012, 1131799087, 1105331604, 1079608267, 1054602088, 1030287313, 1006639361, 983634759, 961251082, 939466903, 918261734, 897615985, 877510909, 857928567, 838851781, 820264098, 802149753, 784493633, 767281247, 750498693, 734132630, 718170251, 702599255, 687407824, 672584601, 658118666, 643999515, 630217042, 616761520, 603623582, 590794206, 578264700, 566026682, 554072074, 542393081, 530982182, 519832118, 508935880, 498286696, 487878024, 477703542, 467757136, 458032893, 448525092, 439228197, 430136849, 421245858, 412550197, 404044996, 395725533, 387587231, 379625653, 371836493, 364215574, 356758843, 349462363, 342322314, 335334983, 328496766, 321804158, 315253754, 308842244, 302566407, 296423115, 290409319]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 8).prefactor = (3475846420217969/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 8).cutoff/(generalMeanRows 8).c)).2 =
    (106552683269607/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 8).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 8).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 8).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 8

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 8).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 8).criticalRate j.val*(generalMeanRows 8).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 8).c*(generalMeanRows 8).criticalPoint j.val)).2-
      (generalMeanRows 8).J/2-(generalMeanRows 8).error (generalMeanGrid j.val)+
      (generalMeanRows 8).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 8).c)).2-
      (generalMeanRows 8).J/2-(generalMeanRows 8).error 4 := by
  have he : (generalMeanRows 8).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 8) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 8)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0008

/-! Kernel-checked entropy margins for general spectral rectangle 9. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0009
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5642980589, 5397863076, 5165637325, 4945500222, 4736707580, 4538568966, 4350443079, 4171733609, 4001885514, 3840381675, 3686739863, 3540510007, 3401271706, 3268631971, 3142223173, 3021701163, 2906743561, 2797048183, 2692331609, 2592327856, 2496787169, 2405474900, 2318170483, 2234666477, 2154767697, 2078290396, 2005061518, 1934918001, 1867706132, 1803280950, 1741505689, 1682251263, 1625395783, 1570824114, 1518427456, 1468102956, 1419753345, 1373286607, 1328615653, 1285658039, 1244335679, 1204574597, 1166304683, 1129459464, 1093975901, 1059794185, 1026857556, 995112125, 964506718, 934992716, 906523916, 879056396, 852548389, 826960162, 802253906, 778393632, 755345071, 733075582, 711554061, 690750868, 670637737, 651187714, 632375083, 614175300, 596564937, 579521620, 563023977, 547051584, 531584922, 516605325, 502094942, 488036692, 474414231, 461211910, 448414744, 436008379, 423979061, 412313606, 400999373, 390024242, 379376583, 369045235, 359019486, 349289051, 339844050, 330674994, 321772760, 313128581, 304734029, 296580993, 288661675, 280968568, 273494447, 266232355, 259175593, 252317707, 245652477, 239173912, 232876233, 226753868, 220801445, 215013778, 209385866, 203912880, 198590160, 193413204, 188377666, 183479346, 178714187, 174078268, 169567798, 165179113, 160908668, 156753036, 152708901, 148773055, 144942393, 141213909, 137584693, 134051929, 130612889]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 9).prefactor = (3604342823579767/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 9).cutoff/(generalMeanRows 9).c)).2 =
    (353640040243591/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 9).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 9).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 9).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 9

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 9).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 9).criticalRate j.val*(generalMeanRows 9).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 9).c*(generalMeanRows 9).criticalPoint j.val)).2-
      (generalMeanRows 9).J/2-(generalMeanRows 9).error (generalMeanGrid j.val)+
      (generalMeanRows 9).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 9).c)).2-
      (generalMeanRows 9).J/2-(generalMeanRows 9).error 4 := by
  have he : (generalMeanRows 9).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 9) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 9)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0009

/-! Kernel-checked entropy margins for general spectral rectangle 10. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0010
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5996375698, 5800820339, 5615151222, 5438725540, 5270949263, 5111272829, 4959187296, 4814220882, 4675935858, 4543925741, 4417812756, 4297245544, 4181897070, 4071462732, 3965658632, 3864220000, 3766899754, 3673467184, 3583706742, 3497416938, 3414409321, 3334507544, 3257546503, 3183371545, 3111837733, 3042809178, 2976158408, 2911765794, 2849519019, 2789312580, 2731047333, 2674630068, 2619973115, 2566993980, 2515615003, 2465763045, 2417369195, 2370368496, 2324699691, 2280304991, 2237129847, 2195122752, 2154235049, 2114420749, 2075636367, 2037840770, 2000995025, 1965062271, 1930007590, 1895797886, 1862401779, 1829789501, 1797932797, 1766804837, 1736380132, 1706634452, 1677544757, 1649089122, 1621246676, 1593997540, 1567322768, 1541204300, 1515624902, 1490568128, 1466018271, 1441960324, 1418379938, 1395263389, 1372597544, 1350369824, 1328568179, 1307181057, 1286197380, 1265606514, 1245398250, 1225562781, 1206090678, 1186972875, 1168200648, 1149765596, 1131659628, 1113874946, 1096404030, 1079239626, 1062374731, 1045802581, 1029516642, 1013510597, 997778335, 982313943, 967111699, 952166057, 937471645, 923023255, 908815835, 894844484, 881104445, 867591095, 854299947, 841226636, 828366921, 815716675, 803271883, 791028636, 778983129, 767131654, 755470598, 743996441, 732705748, 721595170, 710661439, 699901366, 689311839, 678889815, 668632325, 658536468, 648599407, 638818369, 629190644, 619713580, 610384584]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 10).prefactor = (2952209633110281/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 10).cutoff/(generalMeanRows 10).c)).2 =
    (549046836586203/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 10).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 10).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 10).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 10

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 10).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 10).criticalRate j.val*(generalMeanRows 10).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 10).c*(generalMeanRows 10).criticalPoint j.val)).2-
      (generalMeanRows 10).J/2-(generalMeanRows 10).error (generalMeanGrid j.val)+
      (generalMeanRows 10).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 10).c)).2-
      (generalMeanRows 10).J/2-(generalMeanRows 10).error 4 := by
  have he : (generalMeanRows 10).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 10) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 10)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0010

/-! Kernel-checked entropy margins for general spectral rectangle 11. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0011
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6038494422, 5837374025, 5646435608, 5465018444, 5292511906, 5128351052, 4972012662, 4823011690, 4680898065, 4545253813, 4415690447, 4291846612, 4173385939, 4059995100, 3951382032, 3847274319, 3747417716, 3651574791, 3559523691, 3471056999, 3385980696, 3304113194, 3225284457, 3149335184, 3076116061, 3005487064, 2937316821, 2871482020, 2807866860, 2746362546, 2686866816, 2629283509, 2573522159, 2519497618, 2467129713, 2416342917, 2367066050, 2319232000, 2272777462, 2227642695, 2183771295, 2141109988, 2099608429, 2059219025, 2019896758, 1981599029, 1944285512, 1907918009, 1872460323, 1837878140, 1804138911, 1771211749, 1739067327, 1707677788, 1677016659, 1647058766, 1617780161, 1589158049, 1561170723, 1533797502, 1507018668, 1480815417, 1455169801, 1430064688, 1405483707, 1381411214, 1357832247, 1334732489, 1312098235, 1289916357, 1268174274, 1246859921, 1225961724, 1205468572, 1185369795, 1165655139, 1146314745, 1127339129, 1108719165, 1090446062, 1072511352, 1054906874, 1037624753, 1020657393, 1003997462, 987637875, 971571787, 955792581, 940293856, 925069416, 910113265, 895419594, 880982772, 866797344, 852858016, 839159653, 825697270, 812466026, 799461219, 786678278, 774112761, 761760346, 749616829, 737678118, 725940231, 714399286, 703051504, 691893201, 680920787, 670130758, 659519701, 649084280, 638821244, 628727416, 618799695, 609035053, 599430530, 589983233, 580690335, 571549073, 562556743]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 11).prefactor = (1215676435184223/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 11).cutoff/(generalMeanRows 11).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 11).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 11).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 11).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 11

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 11).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 11).criticalRate j.val*(generalMeanRows 11).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 11).c*(generalMeanRows 11).criticalPoint j.val)).2-
      (generalMeanRows 11).J/2-(generalMeanRows 11).error (generalMeanGrid j.val)+
      (generalMeanRows 11).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 11).c)).2-
      (generalMeanRows 11).J/2-(generalMeanRows 11).error 4 := by
  have he : (generalMeanRows 11).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 11) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 11)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0011

/-! Kernel-checked entropy margins for general spectral rectangle 12. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0012
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6216407611, 6009361570, 5812797502, 5626035212, 5448446085, 5279448532, 5118503917, 4965112904, 4818812161, 4679171399, 4545790686, 4418298019, 4296347120, 4179615427, 4067802273, 3960627217, 3857828522, 3759161761, 3664398543, 3573325343, 3485742422, 3401462843, 3320311562, 3242124583, 3166748192, 3094038241, 3023859487, 2956084984, 2890595519, 2827279093, 2766030430, 2706750537, 2649346280, 2593730005, 2539819175, 2487536039, 2436807320, 2387563927, 2339740692, 2293276111, 2248112121, 2204193876, 2161469550, 2119890145, 2079409320, 2039983219, 2001570327, 1964131321, 1927628940, 1892027857, 1857294563, 1823397262, 1790305763, 1757991390, 1726426886, 1695586339, 1665445093, 1635979683, 1607167762, 1578988039, 1551420216, 1524444933, 1498043717, 1472198927, 1446893713, 1422111968, 1397838290, 1374057940, 1350756809, 1327921382, 1305538708, 1283596367, 1262082443, 1240985498, 1220294547, 1199999035, 1180088811, 1160554114, 1141385546, 1122574060, 1104110937, 1085987774, 1068196467, 1050729196, 1033578410, 1016736818, 1000197372, 983953261, 967997894, 952324894, 936928087, 921801494, 906939318, 892335942, 877985917, 863883957, 850024929, 836403851, 823015881, 809856314, 796920577, 784204220, 771702917, 759412454, 747328731, 735447753, 723765630, 712278568, 700982872, 689874935, 678951242, 668208361, 657642943, 647251719, 637031496, 626979157, 617091653, 607366009, 597799313, 588388721, 579131449]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 12).prefactor = (6257470584436529/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 12).cutoff/(generalMeanRows 12).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 12).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 12).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 12).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 12

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 12).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 12).criticalRate j.val*(generalMeanRows 12).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 12).c*(generalMeanRows 12).criticalPoint j.val)).2-
      (generalMeanRows 12).J/2-(generalMeanRows 12).error (generalMeanGrid j.val)+
      (generalMeanRows 12).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 12).c)).2-
      (generalMeanRows 12).J/2-(generalMeanRows 12).error 4 := by
  have he : (generalMeanRows 12).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 12) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 12)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0012

/-! Kernel-checked entropy margins for general spectral rectangle 13. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0013
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6261045034, 6048194331, 5846138953, 5654179661, 5471670209, 5298012664, 5132653215, 4975078426, 4824811845, 4681410965, 4544464463, 4413589704, 4288430481, 4168654949, 4053953755, 3944038321, 3838639286, 3737505071, 3640400570, 3547105950, 3457415543, 3371136834, 3288089522, 3208104667, 3131023888, 3056698635, 2984989511, 2915765647, 2848904120, 2784289422, 2721812957, 2661372589, 2602872204, 2546221326, 2491334737, 2438132144, 2386537855, 2336480485, 2287892683, 2240710872, 2194875012, 2150328376, 2107017347, 2064891217, 2023902016, 1984004333, 1945155168, 1907313781, 1870441555, 1834501866, 1799459967, 1765282875, 1731939264, 1699399368, 1667634890, 1636618916, 1606325832, 1576731255, 1547811953, 1519545787, 1491911645, 1464889385, 1438459779, 1412604464, 1387305893, 1362547290, 1338312607, 1314586483, 1291354213, 1268601703, 1246315446, 1224482487, 1203090393, 1182127227, 1161581524, 1141442263, 1121698846, 1102341077, 1083359142, 1064743589, 1046485310, 1028575524, 1011005761, 993767850, 976853900, 960256288, 943967650, 927980865, 912289044, 896885521, 881763843, 866917759, 852341213, 838028334, 823973428, 810170969, 796615598, 783302107, 770225441, 757380686, 744763065, 732367936, 720190779, 708227201, 696472921, 684923774, 673575701, 662424750, 651467067, 640698896, 630116574, 619716527, 609495270, 599449401, 589575598, 579870619, 570331296, 560954535, 551737314, 542676677, 533769738]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 13).prefactor = (3220917752605343/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 13).cutoff/(generalMeanRows 13).c)).2 =
    (131998356847093/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 13).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 13).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 13).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 13

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 13).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 13).criticalRate j.val*(generalMeanRows 13).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 13).c*(generalMeanRows 13).criticalPoint j.val)).2-
      (generalMeanRows 13).J/2-(generalMeanRows 13).error (generalMeanGrid j.val)+
      (generalMeanRows 13).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 13).c)).2-
      (generalMeanRows 13).J/2-(generalMeanRows 13).error 4 := by
  have he : (generalMeanRows 13).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 13) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 13)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0013

/-! Kernel-checked entropy margins for general spectral rectangle 14. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0014
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6493154019, 6276890556, 6071575711, 5876499006, 5691003841, 5514482736, 5346373076, 5186153294, 5033339431, 4887482044, 4748163394, 4614994919, 4487614923, 4365686487, 4248895557, 4136949206, 4029574046, 3926514769, 3827532816, 3732405154, 3640923155, 3552891559, 3468127528, 3386459766, 3307727716, 3231780812, 3158477791, 3087686055, 3019281084, 2953145893, 2889170519, 2827251561, 2767291742, 2709199502, 2652888632, 2598277919, 2545290822, 2493855178, 2443902914, 2395369790, 2348195158, 2302321729, 2257695372, 2214264906, 2171981927, 2130800627, 2090677643, 2051571902, 2013444482, 1976258484, 1939978909, 1904572544, 1870007855, 1836254887, 1803285173, 1771071644, 1739588549, 1708811377, 1678716787, 1649282539, 1620487433, 1592311245, 1564734681, 1537739315, 1511307545, 1485422549, 1460068238, 1435229218, 1410890751, 1387038721, 1363659599, 1340740413, 1318268717, 1296232564, 1274620479, 1253421436, 1232624835, 1212220479, 1192198551, 1172549602, 1153264524, 1134334542, 1115751189, 1097506297, 1079591981, 1062000622, 1044724862, 1027757584, 1011091905, 994721164, 978638911, 962838901, 947315080, 932061581, 917072712, 902342951, 887866937, 873639466, 859655481, 845910067, 832398448, 819115976, 806058130, 793220512, 780598837, 768188934, 755986737, 743988287, 732189720, 720587273, 709177271, 697956130, 686920354, 676066526, 665391312, 654891456, 644563774, 634405156, 624412564, 614583024, 604913630]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 14).prefactor = (6536045062452579/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 14).cutoff/(generalMeanRows 14).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 14).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 14).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 14).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 14

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 14).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 14).criticalRate j.val*(generalMeanRows 14).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 14).c*(generalMeanRows 14).criticalPoint j.val)).2-
      (generalMeanRows 14).J/2-(generalMeanRows 14).error (generalMeanGrid j.val)+
      (generalMeanRows 14).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 14).c)).2-
      (generalMeanRows 14).J/2-(generalMeanRows 14).error 4 := by
  have he : (generalMeanRows 14).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 14) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 14)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0014

/-! Kernel-checked entropy margins for general spectral rectangle 15. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0015
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8481061156, 8167121097, 7868168576, 7583331537, 7311799800, 7052819570, 6805688554, 6569751607, 6344396845, 6129052146, 5923182009, 5726284723, 5537889797, 5357555633, 5184867419, 5019435197, 4860892108, 4708892782, 4563111871, 4423242692, 4288995983, 4160098766, 4036293282, 3917336023, 3802996829, 3693058051, 3587313780, 3485569127, 3387639555, 3293350260, 3202535593, 3115038518, 3030710114, 2949409102, 2871001409, 2795359756, 2722363276, 2651897154, 2583852290, 2518124985, 2454616641, 2393233486, 2333886312, 2276490227, 2220964429, 2167231981, 2115219615, 2064857533, 2016079227, 1968821309, 1923023348, 1878627718, 1835579455, 1793826121, 1753317675, 1714006352, 1675846549, 1638794718, 1602809260, 1567850433, 1533880255, 1500862422, 1468762222, 1437546463, 1407183390, 1377642625, 1348895094, 1320912967, 1293669600, 1267139475, 1241298149, 1216122201, 1191589187, 1167677593, 1144366789, 1121636991, 1099469222, 1077845271, 1056747661, 1036159617, 1016065027, 996448420, 977294931, 958590278, 940320732, 922473095, 905034674, 887993263, 871337113, 855054923, 839135811, 823569300, 808345300, 793454090, 778886304, 764632914, 750685216, 737034817, 723673622, 710593818, 697787868, 685248493, 672968667, 660941604, 649160746, 637619758, 626312516, 615233098, 604375778, 593735017, 583305456, 573081906, 563059348, 553232917, 543597904, 534149746, 524884022, 515796446, 506882861, 498139238, 489561668]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 15).prefactor = (462875340602437/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 15).cutoff/(generalMeanRows 15).c)).2 =
    (23855065969551/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 15).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 15).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 15).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 15

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 15).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 15).criticalRate j.val*(generalMeanRows 15).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 15).c*(generalMeanRows 15).criticalPoint j.val)).2-
      (generalMeanRows 15).J/2-(generalMeanRows 15).error (generalMeanGrid j.val)+
      (generalMeanRows 15).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 15).c)).2-
      (generalMeanRows 15).J/2-(generalMeanRows 15).error 4 := by
  have he : (generalMeanRows 15).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 15) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 15)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0015

/-! Kernel-checked entropy margins for general spectral rectangle 16. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0016
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7174872853, 6861218683, 6563216231, 6279951832, 6010576630, 5754300808, 5510388462, 5278153036, 5056953231, 4846189351, 4645299999, 4453759113, 4271073275, 4096779277, 3930441908, 3771651941, 3620024291, 3475196339, 3336826389, 3204592257, 3078189976, 2957332595, 2841749083, 2731183307, 2625393098, 2524149372, 2427235332, 2334445711, 2245586084, 2160472214, 2078929455, 2000792186, 1925903293, 1854113674, 1785281789, 1719273226, 1655960308, 1595221711, 1536942121, 1481011902, 1427326783, 1375787574, 1326299893, 1278773905, 1233124087, 1189268996, 1147131060, 1106636373, 1067714509, 1030298339, 994323868, 959730070, 926458739, 894454351, 863663926, 834036901, 805525013, 778082181, 751664405, 726229657, 701737792, 678150451, 655430978, 633544336, 612457034, 592137047, 572553750, 553677852, 535481332, 517937379, 501020337, 484705650, 468969813, 453790320, 439145619, 425015071, 411378906, 398218183, 385514753, 373251224, 361410924, 349977874, 338936752, 328272864, 317972121, 308021005, 298406550, 289116314, 280138357, 271461221, 263073906, 254965850, 247126913, 239547359, 232217832, 225129349, 218273277, 211641322, 205225513, 199018189, 193011984, 187199818, 181574882, 176130628, 170860760, 165759218, 160820175, 156038022, 151407362, 146923002, 142579940, 138373364, 134298638, 130351300, 126527050, 122821748, 119231405, 115752179, 112380365, 109112396, 105944831]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 16).prefactor = (7863351962948147/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 16).cutoff/(generalMeanRows 16).c)).2 =
    (9366996736169/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 16).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 16).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 16).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 16

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 16).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 16).criticalRate j.val*(generalMeanRows 16).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 16).c*(generalMeanRows 16).criticalPoint j.val)).2-
      (generalMeanRows 16).J/2-(generalMeanRows 16).error (generalMeanGrid j.val)+
      (generalMeanRows 16).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 16).c)).2-
      (generalMeanRows 16).J/2-(generalMeanRows 16).error 4 := by
  have he : (generalMeanRows 16).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 16) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 16)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0016

/-! Kernel-checked entropy margins for general spectral rectangle 17. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0017
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6756176856, 6543658204, 6341540418, 6149183406, 5965993558, 5791419685, 5624949405, 5466105893, 5314444971, 5169552482, 5031041921, 4898552288, 4771746143, 4650307834, 4533941885, 4422371524, 4315337335, 4212596024, 4113919291, 4019092786, 3927915154, 3840197151, 3755760835, 3674438811, 3596073537, 3520516681, 3447628525, 3377277414, 3309339238, 3243696961, 3180240176, 3118864688, 3059472137, 3001969633, 2946269428, 2892288599, 2839948761, 2789175794, 2739899587, 2692053804, 2645575658, 2600405704, 2556487644, 2513768146, 2472196670, 2431725307, 2392308633, 2353903560, 2316469211, 2279966790, 2244359466, 2209612262, 2175691957, 2142566979, 2110207322, 2078584455, 2047671244, 2017441870, 1987871767, 1958937542, 1930616922, 1902888687, 1875732616, 1849129435, 1823060762, 1797509064, 1772457611, 1747890431, 1723792274, 1700148572, 1676945404, 1654169463, 1631808023, 1609848909, 1588280472, 1567091558, 1546271483, 1525810013, 1505697339, 1485924053, 1466481132, 1447359919, 1428552100, 1410049692, 1391845025, 1373930726, 1356299706, 1338945145, 1321860479, 1305039389, 1288475788, 1272163810, 1256097802, 1240272309, 1224682072, 1209322010, 1194187220, 1179272964, 1164574663, 1150087889, 1135808361, 1121731933, 1107854593, 1094172456, 1080681757, 1067378847, 1054260186, 1041322341, 1028561981, 1015975871, 1003560870, 991313924, 979232066, 967312412, 955552153, 943948560, 932498974, 921200804, 910051530, 899048692, 888189894]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 17).prefactor = (1412623381930827/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 17).cutoff/(generalMeanRows 17).c)).2 =
    (2088952063271/4000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 17).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 17).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 17).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 17

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 17).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 17).criticalRate j.val*(generalMeanRows 17).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 17).c*(generalMeanRows 17).criticalPoint j.val)).2-
      (generalMeanRows 17).J/2-(generalMeanRows 17).error (generalMeanGrid j.val)+
      (generalMeanRows 17).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 17).c)).2-
      (generalMeanRows 17).J/2-(generalMeanRows 17).error 4 := by
  have he : (generalMeanRows 17).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 17) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 17)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0017

/-! Kernel-checked entropy margins for general spectral rectangle 18. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0018
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6870081346, 6649124418, 6438977321, 6238976021, 6048504698, 5866991534, 5693904958, 5528750277, 5371066656, 5220424393, 5076422459, 4938686275, 4806865689, 4680633141, 4559681993, 4443724995, 4332492895, 4225733156, 4123208782, 4024697243, 3929989478, 3838888987, 3751210981, 3666781606, 3585437225, 3507023745, 3431396007, 3358417208, 3287958370, 3219897846, 3154120862, 3090519086, 3028990234, 2969437695, 2911770189, 2855901439, 2801749875, 2749238346, 2698293864, 2648847352, 2600833415, 2554190126, 2508858821, 2464783912, 2421912710, 2380195255, 2339584164, 2300034482, 2261503544, 2223950847, 2187337929, 2151628253, 2116787102, 2082781476, 2049579998, 2017152825, 1985471562, 1954509188, 1924239974, 1894639419, 1865684181, 1837352016, 1809621716, 1782473061, 1755886757, 1729844394, 1704328397, 1679321983, 1654809118, 1630774479, 1607203417, 1584081924, 1561396596, 1539134605, 1517283669, 1495832026, 1474768403, 1454081996, 1433762443, 1413799807, 1394184549, 1374907510, 1355959896, 1337333255, 1319019463, 1301010710, 1283299478, 1265878535, 1248740917, 1231879915, 1215289066, 1198962137, 1182893119, 1167076213, 1151505821, 1136176538, 1121083144, 1106220591, 1091584002, 1077168656, 1062969987, 1048983575, 1035205139, 1021630531, 1008255732, 995076843, 982090084, 969291787, 956678390, 944246435, 931992562, 919913506, 908006092, 896267233, 884693925, 873283245, 862032347, 850938458, 839998877, 829210973, 818572179]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 18).prefactor = (5874479270049839/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 18).cutoff/(generalMeanRows 18).c)).2 =
    (102023331057081/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 18).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 18).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 18).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 18

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 18).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 18).criticalRate j.val*(generalMeanRows 18).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 18).c*(generalMeanRows 18).criticalPoint j.val)).2-
      (generalMeanRows 18).J/2-(generalMeanRows 18).error (generalMeanGrid j.val)+
      (generalMeanRows 18).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 18).c)).2-
      (generalMeanRows 18).J/2-(generalMeanRows 18).error 4 := by
  have he : (generalMeanRows 18).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 18) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 18)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0018

/-! Kernel-checked entropy margins for general spectral rectangle 19. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0019
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6987340764, 6757724581, 6539343807, 6331509480, 6133582649, 5944970012, 5765120010, 5593519336, 5429689799, 5273185496, 5123590261, 4980515360, 4843597387, 4712496368, 4586894018, 4466492163, 4351011286, 4240189203, 4133779848, 4031552148, 3933289001, 3838786325, 3747852182, 3660305972, 3575977688, 3494707221, 3416343722, 3340745007, 3267777009, 3197313259, 3129234416, 3063427821, 2999787085, 2938211703, 2878606698, 2820882284, 2764953554, 2710740189, 2658166183, 2607159591, 2557652288, 2509579745, 2462880820, 2417497564, 2373375034, 2330461123, 2288706394, 2248063935, 2208489210, 2169939927, 2132375915, 2095759001, 2060052902, 2025223121, 1991236845, 1958062857, 1925671444, 1894034320, 1863124544, 1832916453, 1803385586, 1774508627, 1746263338, 1718628506, 1691583885, 1665110148, 1639188840, 1613802325, 1588933755, 1564567016, 1540686703, 1517278073, 1494327017, 1471820026, 1449744161, 1428087024, 1406836731, 1385981884, 1365511551, 1345415240, 1325682877, 1306304787, 1287271674, 1268574603, 1250204980, 1232154540, 1214415326, 1196979681, 1179840224, 1162989850, 1146421703, 1130129176, 1114105894, 1098345701, 1082842658, 1067591025, 1052585255, 1037819988, 1023290037, 1008990387, 994916180, 981062717, 967425442, 953999942, 940781938, 927767283, 914951949, 902332032, 889903737, 877663382, 865607386, 853732271, 842034656, 830511248, 819158849, 807974342, 796954694, 786096951, 775398233, 764855736, 754466725]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 19).prefactor = (1526835953573329/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 19).cutoff/(generalMeanRows 19).c)).2 =
    (498140464238691/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 19).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 19).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 19).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 19

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 19).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 19).criticalRate j.val*(generalMeanRows 19).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 19).c*(generalMeanRows 19).criticalPoint j.val)).2-
      (generalMeanRows 19).J/2-(generalMeanRows 19).error (generalMeanGrid j.val)+
      (generalMeanRows 19).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 19).c)).2-
      (generalMeanRows 19).J/2-(generalMeanRows 19).error 4 := by
  have he : (generalMeanRows 19).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 19) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 19)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0019

/-! Kernel-checked entropy margins for general spectral rectangle 20. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0020
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7264319173, 7025600997, 6798563603, 6582490716, 6376718060, 6180628812, 5993649550, 5815246620, 5644922875, 5482214736, 5326689542, 5177943146, 5035597741, 4899299873, 4768718642, 4643544054, 4523485511, 4408270437, 4297643012, 4191363003, 4089204702, 3990955937, 3896417161, 3805400617, 3717729557, 3633237526, 3551767695, 3473172245, 3397311793, 3324054858, 3253277367, 3184862197, 3118698740, 3054682508, 2992714759, 2932702147, 2874556401, 2818194016, 2763535975, 2710507480, 2659037706, 2609059565, 2560509494, 2513327244, 2467455696, 2422840675, 2379430788, 2337177261, 2296033792, 2255956415, 2216903364, 2178834954, 2141713465, 2105503030, 2070169537, 2035680530, 2002005121, 1969113900, 1936978860, 1905573319, 1874871848, 1844850205, 1815485272, 1786754994, 1758638323, 1731115167, 1704166337, 1677773501, 1651919139, 1626586502, 1601759573, 1577423023, 1553562187, 1530163018, 1507212066, 1484696439, 1462603783, 1440922250, 1419640472, 1398747542, 1378232988, 1358086750, 1338299164, 1318860940, 1299763145, 1280997185, 1262554788, 1244427993, 1226609128, 1209090804, 1191865895, 1174927532, 1158269086, 1141884160, 1125766576, 1109910367, 1094309768, 1078959205, 1063853287, 1048986798, 1034354689, 1019952074, 1005774217, 991816530, 978074564, 964544007, 951220674, 938100502, 925179549, 912453986, 899920090, 887574246, 875412936, 863432741, 851630332, 840002471, 828546003, 817257859, 806135043, 795174642, 784373810]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 20).prefactor = (6349439116442803/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 20).cutoff/(generalMeanRows 20).c)).2 =
    (498140464238691/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 20).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 20).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 20).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 20

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 20).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 20).criticalRate j.val*(generalMeanRows 20).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 20).c*(generalMeanRows 20).criticalPoint j.val)).2-
      (generalMeanRows 20).J/2-(generalMeanRows 20).error (generalMeanGrid j.val)+
      (generalMeanRows 20).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 20).c)).2-
      (generalMeanRows 20).J/2-(generalMeanRows 20).error 4 := by
  have he : (generalMeanRows 20).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 20) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 20)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0020

/-! Kernel-checked entropy margins for general spectral rectangle 21. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0021
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6788126347, 6542081363, 6308166513, 6085643247, 5873826548, 5672080245, 5479812829, 5296473714, 5121549871, 4954562801, 4795065806, 4642641509, 4496899620, 4357474890, 4224025256, 4096230147, 3973788937, 3856419521, 3743857019, 3635852580, 3532172280, 3432596111, 3336917049, 3244940188, 3156481946, 3071369327, 2989439234, 2910537840, 2834519996, 2761248689, 2690594528, 2622435279, 2556655418, 2493145723, 2431802894, 2372529195, 2315232119, 2259824079, 2206222117, 2154347629, 2104126115, 2055486939, 2008363105, 1962691045, 1918410432, 1875463984, 1833797303, 1793358705, 1754099071, 1715971703, 1678932193, 1642938292, 1607949796, 1573928429, 1540837745, 1508643022, 1477311174, 1446810662, 1417111409, 1388184728, 1360003242, 1332540819, 1305772506, 1279674466, 1254223925, 1229399109, 1205179200, 1181544284, 1158475305, 1135954021, 1113962964, 1092485402, 1071505300, 1051007287, 1030976622, 1011399164, 992261344, 973550132, 955253019, 937357983, 919853474, 902728384, 885972032, 869574141, 853524819, 837814544, 822434141, 807374772, 792627920, 778185369, 764039196, 750181756, 736605671, 723303814, 710269302, 697495486, 684975936, 672704437, 660674976, 648881735, 637319085, 625981572, 614863915, 603960999, 593267865, 582779705, 572491858, 562399800, 552499142, 542785624, 533255111, 523903583, 514727138, 505721982, 496884428, 488210890, 479697881, 471342009, 463139971, 455088554, 447184629]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 21).prefactor = (660113108403393/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 21).cutoff/(generalMeanRows 21).c)).2 =
    (440320893349863/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 21).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 21).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 21).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 21

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 21).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 21).criticalRate j.val*(generalMeanRows 21).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 21).c*(generalMeanRows 21).criticalPoint j.val)).2-
      (generalMeanRows 21).J/2-(generalMeanRows 21).error (generalMeanGrid j.val)+
      (generalMeanRows 21).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 21).c)).2-
      (generalMeanRows 21).J/2-(generalMeanRows 21).error 4 := by
  have he : (generalMeanRows 21).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 21) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 21)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0021

/-! Kernel-checked entropy margins for general spectral rectangle 22. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0022
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6013522851, 5765535644, 5530111044, 5306487372, 5093957974, 4891866400, 4699602101, 4516596576, 4342319919, 4176277698, 4018008156, 3867079663, 3723088416, 3585656343, 3454429199, 3329074824, 3209281556, 3094756773, 2985225563, 2880429494, 2780125488, 2684084787, 2592091990, 2503944173, 2419450072, 2338429328, 2260711781, 2186136830, 2114552825, 2045816507, 1979792489, 1916352774, 1855376301, 1796748526, 1740361031, 1686111158, 1633901665, 1583640413, 1535240063, 1488617797, 1443695061, 1400397317, 1358653813, 1318397374, 1279564192, 1242093647, 1205928122, 1171012839, 1137295705, 1104727159, 1073260041, 1042849458, 1013452661, 985028934, 957539481, 930947325, 905217216, 880315534, 856210211, 832870642, 810267615, 788373240, 767160877, 746605075, 726681510, 707366932, 688639106, 670476763, 652859556, 635768007, 619183472, 603088094, 587464768, 572297103, 557569390, 543266566, 529374185, 515878389, 502765881, 490023896, 477640177, 465602953, 453900917, 442523202, 431459362, 420699353, 410233516, 400052559, 390147540, 380509850, 371131203, 362003616, 353119403, 344471154, 336051728, 327854242, 319872057, 312098770, 304528202, 297154392, 289971584, 282974222, 276156938, 269514550, 263042049, 256734593, 250587503, 244596254, 238756472, 233063924, 227514514, 222104280, 216829386, 211686119, 206670882, 201780192, 197010676, 192359065, 187822191, 183396982, 179080463]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 22).prefactor = (6862800129188623/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 22).cutoff/(generalMeanRows 22).c)).2 =
    (17712314228931/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 22).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 22).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 22).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 22

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 22).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 22).criticalRate j.val*(generalMeanRows 22).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 22).c*(generalMeanRows 22).criticalPoint j.val)).2-
      (generalMeanRows 22).J/2-(generalMeanRows 22).error (generalMeanGrid j.val)+
      (generalMeanRows 22).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 22).c)).2-
      (generalMeanRows 22).J/2-(generalMeanRows 22).error 4 := by
  have he : (generalMeanRows 22).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 22) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 22)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0022

/-! Kernel-checked entropy margins for general spectral rectangle 23. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0023
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6126702914, 5929588365, 5742232134, 5564016213, 5394368562, 5232759078, 5078695992, 4931722641, 4791414555, 4657376844, 4529241824, 4406666871, 4289332476, 4176940470, 4069212411, 3965888112, 3866724291, 3771493337, 3679982183, 3591991263, 3507333560, 3425833725, 3347327272, 3271659823, 3198686427, 3128270914, 3060285315, 2994609306, 2931129709, 2869740021, 2810339977, 2752835148, 2697136563, 2643160362, 2590827468, 2540063289, 2490797431, 2442963439, 2396498549, 2351343464, 2307442136, 2264741570, 2223191637, 2182744901, 2143356453, 2104983767, 2067586549, 2031126610, 1995567739, 1960875587, 1927017557, 1893962704, 1861681638, 1830146431, 1799330538, 1769208714, 1739756942, 1710952362, 1682773205, 1655198735, 1628209187, 1601785716, 1575910343, 1550565911, 1525736037, 1501405070, 1477558055, 1454180688, 1431259288, 1408780761, 1386732567, 1365102695, 1343879631, 1323052334, 1302610211, 1282543095, 1262841220, 1243495205, 1224496032, 1205835024, 1187503838, 1169494437, 1151799083, 1134410317, 1117320951, 1100524050, 1084012920, 1067781101, 1051822353, 1036130643, 1020700140, 1005525206, 990600381, 975920382, 961480092, 947274550, 933298950, 919548629, 906019064, 892705865, 879604769, 866711634, 854022435, 841533262, 829240308, 817139872, 805228352, 793502240, 781958119, 770592663, 759402628, 748384851, 737536248, 726853812, 716334607, 705975767, 695774495, 685728058, 675833787, 666089073, 656491366]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 23).prefactor = (710026367130571/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 23).cutoff/(generalMeanRows 23).c)).2 =
    (52988916255327/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 23).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 23).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 23).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 23

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 23).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 23).criticalRate j.val*(generalMeanRows 23).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 23).c*(generalMeanRows 23).criticalPoint j.val)).2-
      (generalMeanRows 23).J/2-(generalMeanRows 23).error (generalMeanGrid j.val)+
      (generalMeanRows 23).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 23).c)).2-
      (generalMeanRows 23).J/2-(generalMeanRows 23).error 4 := by
  have he : (generalMeanRows 23).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 23) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 23)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0023

/-! Kernel-checked entropy margins for general spectral rectangle 24. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0024
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6184302498, 5981147944, 5788061673, 5604407271, 5429595634, 5263080823, 5104356352, 4952951866, 4808430143, 4670384401, 4538435856, 4412231516, 4291442174, 4175760586, 4064899808, 3958591680, 3856585439, 3758646453, 3664555051, 3574105462, 3487104824, 3403372289, 3322738183, 3245043239, 3170137891, 3097881613, 3028142317, 2960795789, 2895725167, 2832820464, 2771978113, 2713100556, 2656095857, 2600877341, 2547363260, 2495476482, 2445144204, 2396297677, 2348871956, 2302805666, 2258040784, 2214522428, 2172198675, 2131020374, 2090940982, 2051916411, 2013904877, 1976866764, 1940764499, 1905562430, 1871226712, 1837725206, 1805027376, 1773104199, 1741928077, 1711472758, 1681713255, 1652625780, 1624187671, 1596377333, 1569174179, 1542558569, 1516511763, 1491015869, 1466053798, 1441609219, 1417666518, 1394210763, 1371227663, 1348703534, 1326625272, 1304980316, 1283756626, 1262942650, 1242527303, 1222499940, 1202850338, 1183568668, 1164645482, 1146071691, 1127838543, 1109937616, 1092360793, 1075100250, 1058148445, 1041498100, 1025142190, 1009073934, 993286777, 977774386, 962530638, 947549609, 932825564, 918352952, 904126396, 890140686, 876390769, 862871747, 849578866, 836507512, 823653206, 811011595, 798578450, 786349662, 774321231, 762489270, 750849993, 739399717, 728134854, 717051909, 706147477, 695418238, 684860956, 674472474, 664249711, 654189663, 644289396, 634546045, 624956811, 615518961, 606229825]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 24).prefactor = (1464646614651589/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 24).cutoff/(generalMeanRows 24).c)).2 =
    (519193873436521/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 24).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 24).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 24).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 24

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 24).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 24).criticalRate j.val*(generalMeanRows 24).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 24).c*(generalMeanRows 24).criticalPoint j.val)).2-
      (generalMeanRows 24).J/2-(generalMeanRows 24).error (generalMeanGrid j.val)+
      (generalMeanRows 24).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 24).c)).2-
      (generalMeanRows 24).J/2-(generalMeanRows 24).error 4 := by
  have he : (generalMeanRows 24).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 24) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 24)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0024

/-! Kernel-checked entropy margins for general spectral rectangle 25. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0025
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6243444585, 6034151333, 5835246104, 5646073455, 5466026641, 5294543346, 5131101867, 4975217684, 4826440384, 4684350882, 4548558910, 4418700743, 4294437139, 4175451456, 4061447949, 3952150202, 3847299708, 3746654557, 3649988244, 3557088562, 3467756600, 3381805806, 3299061133, 3219358245, 3142542794, 3068469737, 2997002718, 2928013487, 2861381366, 2796992751, 2734740654, 2674524273, 2616248595, 2559824028, 2505166052, 2452194906, 2400835285, 2351016062, 2302670031, 2255733667, 2210146892, 2165852877, 2122797833, 2080930836, 2040203650, 2000570569, 1961988264, 1924415645, 1887813730, 1852145515, 1817375867, 1783471411, 1750400428, 1718132762, 1686639730, 1655894036, 1625869697, 1596541964, 1567887257, 1539883097, 1512508046, 1485741649, 1459564382, 1433957598, 1408903482, 1384385005, 1360385880, 1336890526, 1313884028, 1291352103, 1269281063, 1247657792, 1226469707, 1205704738, 1185351296, 1165398252, 1145834914, 1126651003, 1107836631, 1089382287, 1071278814, 1053517392, 1036089524, 1018987017, 1002201971, 985726764, 969554036, 953676681, 938087834, 922780857, 907749333, 892987053, 878488008, 864246380, 850256533, 836513006, 823010504, 809743893, 796708192, 783898565, 771310318, 758938892, 746779856, 734828905, 723081850, 711534620, 700183252, 689023889, 678052775, 667266255, 656660764, 646232831, 635979071, 625896184, 615980949, 606230227, 596640953, 587210135, 577934851, 568812249, 559839542]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 25).prefactor = (6042563502197009/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 25).cutoff/(generalMeanRows 25).c)).2 =
    (508611764105983/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 25).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 25).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 25).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 25

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 25).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 25).criticalRate j.val*(generalMeanRows 25).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 25).c*(generalMeanRows 25).criticalPoint j.val)).2-
      (generalMeanRows 25).J/2-(generalMeanRows 25).error (generalMeanGrid j.val)+
      (generalMeanRows 25).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 25).c)).2-
      (generalMeanRows 25).J/2-(generalMeanRows 25).error 4 := by
  have he : (generalMeanRows 25).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 25) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 25)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0025

/-! Kernel-checked entropy margins for general spectral rectangle 26. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0026
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5800005134, 5586545027, 5383812636, 5191135821, 5007892230, 4833504928, 4667438493, 4509195511, 4358313427, 4214361701, 4076939247, 3945672109, 3820211348, 3700231127, 3585426968, 3475514149, 3370226259, 3269313853, 3172543238, 3079695346, 2990564705, 2904958489, 2822695644, 2743606081, 2667529929, 2594316854, 2523825415, 2455922477, 2390482669, 2327387873, 2266526754, 2207794329, 2151091556, 2096324959, 2043406279, 1992252145, 1942783772, 1894926675, 1848610407, 1803768311, 1760337290, 1718257593, 1677472611, 1637928696, 1599574977, 1562363203, 1526247582, 1491184647, 1457133111, 1424053748, 1391909272, 1360664225, 1330284877, 1300739122, 1271996394, 1244027576, 1216804922, 1190301977, 1164493512, 1139355454, 1114864822, 1090999669, 1067739028, 1045062857, 1022951991, 1001388098, 980353630, 959831787, 939806477, 920262278, 901184404, 882558675, 864371484, 846609769, 829260987, 812313084, 795754479, 779574030, 763761025, 748305152, 733196482, 718425453, 703982854, 689859802, 676047734, 662538389, 649323793, 636396250, 623748326, 611372838, 599262844, 587411633, 575812714, 564459803, 553346823, 542467887, 531817293, 521389519, 511179209, 501181174, 491390380, 481801944, 472411127, 463213329, 454204085, 445379056, 436734028, 428264906, 419967709, 411838566, 403873713, 396069488, 388422328, 380928765, 373585424, 366389016, 359336342, 352424283, 345649799, 339009931, 332501792]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 26).prefactor = (3116158986136139/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 26).cutoff/(generalMeanRows 26).c)).2 =
    (228659234859217/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 26).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 26).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 26).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 26

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 26).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 26).criticalRate j.val*(generalMeanRows 26).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 26).c*(generalMeanRows 26).criticalPoint j.val)).2-
      (generalMeanRows 26).J/2-(generalMeanRows 26).error (generalMeanGrid j.val)+
      (generalMeanRows 26).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 26).c)).2-
      (generalMeanRows 26).J/2-(generalMeanRows 26).error 4 := by
  have he : (generalMeanRows 26).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 26) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 26)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0026

/-! Kernel-checked entropy margins for general spectral rectangle 27. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0027
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5518057631, 5301051084, 5095108955, 4899540126, 4713704542, 4537008729, 4368901785, 4208871788, 4056442566, 3911170785, 3772643318, 3640474866, 3514305794, 3393800165, 3278643954, 3168543413, 3063223580, 2962426908, 2865912021, 2773452559, 2684836120, 2599863295, 2518346767, 2440110485, 2364988906, 2292826284, 2223476024, 2156800076, 2092668376, 2030958326, 1971554317, 1914347278, 1859234263, 1806118064, 1754906852, 1705513842, 1657856982, 1611858661, 1567445440, 1524547797, 1483099893, 1443039349, 1404307042, 1366846912, 1330605781, 1295533185, 1261581215, 1228704372, 1196859425, 1166005283, 1136102875, 1107115032, 1079006385, 1051743259, 1025293584, 999626802, 974713787, 950526767, 927039246, 904225941, 882062714, 860526510, 839595304, 819248039, 799464583, 780225678, 761512892, 743308583, 725595850, 708358503, 691581025, 675248536, 659346762, 643862008, 628781127, 614091494, 599780978, 585837924, 572251125, 559009804, 546103592, 533522509, 521256947, 509297653, 497635711, 486262528, 475169820, 464349597, 453794151, 443496043, 433448091, 423643360, 414075149, 404736986, 395622613, 386725979, 378041233, 369562712, 361284939, 353202610, 345310590, 337603905, 330077737, 322727418, 315548420, 308536358, 301686975, 294996144, 288459861, 282074240, 275835508, 269740003, 263784169, 257964552, 252277796, 246720640, 241289916, 235982543, 230795527, 225725955, 220770996]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 27).prefactor = (3214015648605561/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 27).cutoff/(generalMeanRows 27).c)).2 =
    (418097756565151/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 27).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 27).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 27).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 27

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 27).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 27).criticalRate j.val*(generalMeanRows 27).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 27).c*(generalMeanRows 27).criticalPoint j.val)).2-
      (generalMeanRows 27).J/2-(generalMeanRows 27).error (generalMeanGrid j.val)+
      (generalMeanRows 27).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 27).c)).2-
      (generalMeanRows 27).J/2-(generalMeanRows 27).error 4 := by
  have he : (generalMeanRows 27).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 27) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 27)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0027

/-! Kernel-checked entropy margins for general spectral rectangle 28. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0028
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5471486054, 5249607983, 5039136370, 4839359206, 4649617023, 4469298284, 4297835258, 4134700324, 3979402651, 3831485197, 3690522010, 3556115773, 3427895584, 3305514933, 3188649864, 3076997294, 2970273478, 2868212603, 2770565504, 2677098480, 2587592207, 2501840740, 2419650589, 2340839875, 2265237542, 2192682632, 2123023618, 2056117780, 1991830631, 1930035385, 1870612462, 1813449027, 1758438562, 1705480472, 1654479713, 1605346447, 1557995723, 1512347179, 1468324758, 1425856453, 1384874063, 1345312961, 1307111891, 1270212760, 1234560457, 1200102682, 1166789777, 1134574578, 1103412273, 1073260263, 1044078044, 1015827082, 988470708, 961974013, 936303748, 911428238, 887317289, 863942115, 841275257, 819290512, 797962868, 777268441, 757184413, 737688977, 718761287, 700381403, 682530251, 665189571, 648341884, 631970445, 616059211, 600592804, 585556479, 570936092, 556718071, 542889388, 529437533, 516350490, 503616712, 491225099, 479164979, 467426086, 455998541, 444872836, 434039816, 423490663, 413216882, 403210285, 393462978, 383967349, 374716053, 365702006, 356918366, 348358531, 340016121, 331884976, 323959141, 316232861, 308700572, 301356891, 294196614, 287214702, 280406281, 273766632, 267291184, 260975511, 254815326, 248806472, 242944925, 237226780, 231648251, 226205669, 220895474, 215714209, 210658525, 205725166, 200910976, 196212888, 191627924, 187153192, 182785883]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 28).prefactor = (6629890602783341/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 28).cutoff/(generalMeanRows 28).c)).2 =
    (399049561594459/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 28).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 28).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 28).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 28

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 28).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 28).criticalRate j.val*(generalMeanRows 28).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 28).c*(generalMeanRows 28).criticalPoint j.val)).2-
      (generalMeanRows 28).J/2-(generalMeanRows 28).error (generalMeanGrid j.val)+
      (generalMeanRows 28).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 28).c)).2-
      (generalMeanRows 28).J/2-(generalMeanRows 28).error 4 := by
  have he : (generalMeanRows 28).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 28) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 28)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0028

/-! Kernel-checked entropy margins for general spectral rectangle 29. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0029
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5643306994, 5414461291, 5197380243, 4991329482, 4795628830, 4609647546, 4432800071, 4264542215, 4104367732, 3951805231, 3806415380, 3667788387, 3535541703, 3409317935, 3288782956, 3173624163, 3063548901, 2958283011, 2857569503, 2761167337, 2668850300, 2580405982, 2495634816, 2414349211, 2336372740, 2261539390, 2189692876, 2120685995, 2054380038, 1990644238, 1929355258, 1870396721, 1813658764, 1759037633, 1706435298, 1655759101, 1606921424, 1559839379, 1514434523, 1470632588, 1428363228, 1387559791, 1348159093, 1310101219, 1273329328, 1237789476, 1203430447, 1170203595, 1138062701, 1106963828, 1076865200, 1047727074, 1019511629, 992182859, 965706471, 940049796, 915181692, 891072468, 867693803, 845018671, 823021276, 801676982, 780962256, 760854606, 741332529, 722375463, 703963731, 686078503, 668701748, 651816197, 635405303, 619453205, 603944695, 588865184, 574200674, 559937729, 546063446, 532565431, 519431775, 506651028, 494212185, 482104655, 470318251, 458843166, 447669957, 436789530, 426193121, 415872287, 405818886, 396025066, 386483252, 377186136, 368126664, 359298025, 350693639, 342307152, 334132422, 326163514, 318394688, 310820394, 303435262, 296234098, 289211873, 282363719, 275684922, 269170919, 262817285, 256619736, 250574118, 244676406, 238922695, 233309200, 227832249, 222488277, 217273829, 212185548, 207220178, 202374556, 197645610, 193030359, 188525904]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 29).prefactor = (6838088891064583/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 29).cutoff/(generalMeanRows 29).c)).2 =
    (399049561594459/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 29).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 29).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 29).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 29

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 29).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 29).criticalRate j.val*(generalMeanRows 29).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 29).c*(generalMeanRows 29).criticalPoint j.val)).2-
      (generalMeanRows 29).J/2-(generalMeanRows 29).error (generalMeanGrid j.val)+
      (generalMeanRows 29).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 29).c)).2-
      (generalMeanRows 29).J/2-(generalMeanRows 29).error 4 := by
  have he : (generalMeanRows 29).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 29) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 29)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0029

/-! Kernel-checked entropy margins for general spectral rectangle 30. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0030
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6999899868, 6784492646, 6579360181, 6383886278, 6197498828, 6019665965, 5849892630, 5687717502, 5532710244, 5384469020, 5242618263, 5106806648, 4976705257, 4852005914, 4732419662, 4617675382, 4507518519, 4401709929, 4300024806, 4202251711, 4108191663, 4017657316, 3930472188, 3846469956, 3765493798, 3687395789, 3612036335, 3539283655, 3469013293, 3401107665, 3335455645, 3271952167, 3210497863, 3150998724, 3093365781, 3037514805, 2983366034, 2930843913, 2879876847, 2830396977, 2782339962, 2735644786, 2690253563, 2646111366, 2603166058, 2561368139, 2520670599, 2481028781, 2442400250, 2404744674, 2368023709, 2332200890, 2297241531, 2263112629, 2229782774, 2197222062, 2165402020, 2134295525, 2103876736, 2074121026, 2045004916, 2016506022, 1988602989, 1961275445, 1934503947, 1908269933, 1882555681, 1857344259, 1832619493, 1808365920, 1784568760, 1761213878, 1738287750, 1715777436, 1693670550, 1671955230, 1650620116, 1629654321, 1609047412, 1588789386, 1568870649, 1549281994, 1530014587, 1511059945, 1492409923, 1474056692, 1455992731, 1438210807, 1420703963, 1403465507, 1386488997, 1369768230, 1353297232, 1337070247, 1321081726, 1305326319, 1289798863, 1274494378, 1259408057, 1244535254, 1229871484, 1215412412, 1201153845, 1187091728, 1173222138, 1159541278, 1146045471, 1132731155, 1119594877, 1106633292, 1093843154, 1081221316, 1068764721, 1056470402, 1044335480, 1032357155, 1020532705, 1008859486, 997334925, 985956517, 974721827]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 30).prefactor = (2743047204925973/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 30).cutoff/(generalMeanRows 30).c)).2 =
    (505520571536313/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 30).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 30).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 30).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 30

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 30).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 30).criticalRate j.val*(generalMeanRows 30).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 30).c*(generalMeanRows 30).criticalPoint j.val)).2-
      (generalMeanRows 30).J/2-(generalMeanRows 30).error (generalMeanGrid j.val)+
      (generalMeanRows 30).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 30).c)).2-
      (generalMeanRows 30).J/2-(generalMeanRows 30).error 4 := by
  have he : (generalMeanRows 30).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 30) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 30)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0030

/-! Kernel-checked entropy margins for general spectral rectangle 31. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0031
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7141727462, 6917062418, 6703105804, 6499216546, 6304799440, 6119301145, 5942206607, 5773035868, 5611341195, 5456704503, 5308735024, 5167067201, 5031358785, 4901289089, 4776557418, 4656881621, 4541996774, 4431653972, 4325619225, 4223672433, 4125606455, 4031226242, 3940348042, 3852798664, 3768414797, 3687042374, 3608535995, 3532758380, 3459579862, 3388877923, 3320536754, 3254446849, 3190504627, 3128612075, 3068676423, 3010609829, 2954329095, 2899755397, 2846814028, 2795434167, 2745548654, 2697093782, 2650009102, 2604237243, 2559723733, 2516416847, 2474267447, 2433228844, 2393256661, 2354308711, 2316344872, 2279326980, 2243218723, 2207985538, 2173594522, 2140014342, 2107215152, 2075168513, 2043847321, 2013225736, 1983279118, 1953983960, 1925317834, 1897259336, 1869788026, 1842884389, 1816529779, 1790706380, 1765397162, 1740585841, 1716256843, 1692395267, 1668986853, 1646017949, 1623475479, 1601346919, 1579620267, 1558284018, 1537327138, 1516739045, 1496509584, 1476629008, 1457087955, 1437877436, 1418988812, 1400413778, 1382144350, 1364172846, 1346491876, 1329094325, 1311973342, 1295122328, 1278534921, 1262204992, 1246126628, 1230294123, 1214701975, 1199344866, 1184217665, 1169315411, 1154633311, 1140166730, 1125911185, 1111862337, 1098015986, 1084368068, 1070914642, 1057651891, 1044576115, 1031683725, 1018971239, 1006435278, 994072562, 981879905, 969854212, 957992475, 946291770, 934749251, 923362153, 912127782, 901043515]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 31).prefactor = (142997943685943/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 31).cutoff/(generalMeanRows 31).c)).2 =
    (493250478944497/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 31).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 31).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 31).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 31

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 31).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 31).criticalRate j.val*(generalMeanRows 31).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 31).c*(generalMeanRows 31).criticalPoint j.val)).2-
      (generalMeanRows 31).J/2-(generalMeanRows 31).error (generalMeanGrid j.val)+
      (generalMeanRows 31).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 31).c)).2-
      (generalMeanRows 31).J/2-(generalMeanRows 31).error 4 := by
  have he : (generalMeanRows 31).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 31) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 31)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0031

/-! Kernel-checked entropy margins for general spectral rectangle 32. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0032
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7287950385, 7053747577, 6830705898, 6618158303, 6415485472, 6222111637, 6037500863, 5861153722, 5692604311, 5531417563, 5377186826, 5229531673, 5088095911, 4952545780, 4822568307, 4697869806, 4578174504, 4463223289, 4352772555, 4246593142, 4144469364, 4046198111, 3951588018, 3860458700, 3772640046, 3687971560, 3606301753, 3527487582, 3451393920, 3377893073, 3306864322, 3238193506, 3171772621, 3107499455, 3045277249, 2985014367, 2926624006, 2870023908, 2815136100, 2761886651, 2710205435, 2660025921, 2611284967, 2563922631, 2517881992, 2473108981, 2429552226, 2387162902, 2345894590, 2305703149, 2266546591, 2228384965, 2191180246, 2154896233, 2119498454, 2084954070, 2051231792, 2018301797, 1986135654, 1954706246, 1923987710, 1893955363, 1864585648, 1835856072, 1807745153, 1780232369, 1753298107, 1726923621, 1701090982, 1675783044, 1650983399, 1626676345, 1602846846, 1579480503, 1556563522, 1534082681, 1512025306, 1490379244, 1469132834, 1448274887, 1427794662, 1407681845, 1387926528, 1368519188, 1349450673, 1330712182, 1312295247, 1294191721, 1276393760, 1258893812, 1241684598, 1224759108, 1208110581, 1191732497, 1175618568, 1159762721, 1144159097, 1128802036, 1113686069, 1098805910, 1084156449, 1069732742, 1055530007, 1041543613, 1027769079, 1014202062, 1000838354, 987673878, 974704677, 961926916, 949336871, 936930930, 924705582, 912657420, 900783131, 889079494, 877543380, 866171743, 854961619, 843910125, 833014452]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 32).prefactor = (5963706891135313/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 32).cutoff/(generalMeanRows 32).c)).2 =
    (240564559206077/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 32).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 32).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 32).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 32

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 32).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 32).criticalRate j.val*(generalMeanRows 32).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 32).c*(generalMeanRows 32).criticalPoint j.val)).2-
      (generalMeanRows 32).J/2-(generalMeanRows 32).error (generalMeanGrid j.val)+
      (generalMeanRows 32).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 32).c)).2-
      (generalMeanRows 32).J/2-(generalMeanRows 32).error 4 := by
  have he : (generalMeanRows 32).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 32) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 32)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0032

/-! Kernel-checked entropy margins for general spectral rectangle 33. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0033
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7438718447, 7194688458, 6962291982, 6740834858, 6529672582, 6328205968, 6135877269, 5952166723, 5776589442, 5608692616, 5448052995, 5294274607, 5146986690, 5005841813, 4870514167, 4740698001, 4616106198, 4496468966, 4381532639, 4271058579, 4164822157, 4062611823, 3964228243, 3869483501, 3778200364, 3690211602, 3605359350, 3523494525, 3444476279, 3368171494, 3294454306, 3223205671, 3154312950, 3087669530, 3023174464, 2960732142, 2900251973, 2841648102, 2784839128, 2729747853, 2676301044, 2624429203, 2574066362, 2525149882, 2477620268, 2431420994, 2386498340, 2342801238, 2300281127, 2258891816, 2218589355, 2179331917, 2141079681, 2103794726, 2067440931, 2031983877, 1997390762, 1963630310, 1930672696, 1898489466, 1867053473, 1836338801, 1806320706, 1776975559, 1748280781, 1720214796, 1692756981, 1665887611, 1639587820, 1613839558, 1588625546, 1563929240, 1539734798, 1516027039, 1492791416, 1470013981, 1447681359, 1425780720, 1404299749, 1383226627, 1362550000, 1342258966, 1322343046, 1302792166, 1283596639, 1264747149, 1246234727, 1228050743, 1210186884, 1192635143, 1175387803, 1158437426, 1141776839, 1125399122, 1109297595, 1093465812, 1077897547, 1062586784, 1047527711, 1032714707, 1018142338, 1003805343, 989698635, 975817287, 962156526, 948711728, 935478414, 922452240, 909628991, 897004581, 884575043, 872336524, 860285286, 848417694, 836730217, 825219423, 813881972, 802714619, 791714203, 780877648, 770201960]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 33).prefactor = (6217886594489377/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 33).cutoff/(generalMeanRows 33).c)).2 =
    (469152927365437/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 33).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 33).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 33).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 33

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 33).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 33).criticalRate j.val*(generalMeanRows 33).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 33).c*(generalMeanRows 33).criticalPoint j.val)).2-
      (generalMeanRows 33).J/2-(generalMeanRows 33).error (generalMeanGrid j.val)+
      (generalMeanRows 33).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 33).c)).2-
      (generalMeanRows 33).J/2-(generalMeanRows 33).error 4 := by
  have he : (generalMeanRows 33).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 33) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 33)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0033

/-! Kernel-checked entropy margins for general spectral rectangle 34. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0034
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6722235700, 6471729798, 6233330278, 6006320509, 5790035024, 5583855027, 5387204407, 5199546155, 5020379163, 4849235343, 4685677022, 4529294593, 4379704387, 4236546733, 4099484202, 3968199992, 3842396469, 3721793813, 3606128792, 3495153626, 3388634946, 3286352835, 3188099940, 3093680656, 3002910372, 2915614764, 2831629153, 2750797899, 2672973840, 2598017776, 2525797983, 2456189761, 2389075016, 2324341866, 2261884277, 2201601722, 2143398856, 2087185225, 2032874980, 1980386620, 1929642740, 1880569807, 1833097943, 1787160719, 1742694967, 1699640602, 1657940452, 1617540102, 1578387744, 1540434035, 1503631973, 1467936763, 1433305707, 1399698092, 1367075086, 1335399640, 1304636396, 1274751599, 1245713017, 1217489861, 1190052712, 1163373453, 1137425203, 1112182253, 1087620013, 1063714949, 1040444536, 1017787208, 995722310, 974230053, 953291474, 932888393, 913003379, 893619713, 874721352, 856292901, 838319579, 820787190, 803682101, 786991208, 770701918, 754802123, 739280177, 724124877, 709325442, 694871492, 680753034, 666960443, 653484444, 640316098, 627446790, 614868210, 602572341, 590551449, 578798070, 567304997, 556065269, 545072163, 534319182, 523800047, 513508685, 503439225, 493585987, 483943475, 474506369, 465269519, 456227936, 447376790, 438711399, 430227225, 421919870, 413785070, 405818686, 398016707, 390375236, 382890494, 375558811, 368376623, 361340467, 354446980, 347692894]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 34).prefactor = (3241449857252337/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 34).cutoff/(generalMeanRows 34).c)).2 =
    (389110219691899/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 34).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 34).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 34).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 34

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 34).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 34).criticalRate j.val*(generalMeanRows 34).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 34).c*(generalMeanRows 34).criticalPoint j.val)).2-
      (generalMeanRows 34).J/2-(generalMeanRows 34).error (generalMeanGrid j.val)+
      (generalMeanRows 34).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 34).c)).2-
      (generalMeanRows 34).J/2-(generalMeanRows 34).error 4 := by
  have he : (generalMeanRows 34).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 34) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 34)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0034

/-! Kernel-checked entropy margins for general spectral rectangle 35. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0035
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5918440527, 5667676228, 5429457828, 5203042818, 4987741534, 4782912527, 4587958429, 4402322261, 4225484123, 4056958216, 3896290157, 3743054555, 3596852807, 3457311107, 3324078624, 3196825848, 3075243072, 2959039009, 2847939519, 2741686443, 2640036528, 2542760438, 2449641845, 2360476581, 2275071862, 2193245566, 2114825567, 2039649107, 1967562228, 1898419232, 1832082182, 1768420438, 1707310228, 1648634237, 1592281235, 1538145724, 1486127607, 1436131879, 1388068343, 1341851336, 1297399473, 1254635417, 1213485649, 1173880261, 1135752761, 1099039886, 1063681427, 1029620071, 996801239, 965172948, 934685672, 905292213, 876947580, 849608875, 823235185, 797787480, 773228518, 749522753, 726636251, 704536607, 683192869, 662575467, 642656144, 623407890, 604804882, 586822427, 569436905, 552625718, 536367241, 520640774, 505426501, 490705445, 476459430, 462671040, 449323589, 436401082, 423888187, 411770200, 400033019, 388663116, 377647510, 366973743, 356629856, 346604366, 336886247, 327464906, 318330166, 309472248, 300881752, 292549643, 284467230, 276626158, 269018387, 261636182, 254472102, 247518980, 240769920, 234218280, 227857663, 221681909, 215685079, 209861454, 204205519, 198711958, 193375646, 188191640, 183155173, 178261644, 173506616, 168885806, 164395078, 160030443, 155788046, 151664165, 147655204, 143757692, 139968272, 136283700, 132700844, 129216671, 125828253]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 35).prefactor = (1689801995808841/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 35).cutoff/(generalMeanRows 35).c)).2 =
    (147399770110331/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 35).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 35).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 35).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 35

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 35).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 35).criticalRate j.val*(generalMeanRows 35).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 35).c*(generalMeanRows 35).criticalPoint j.val)).2-
      (generalMeanRows 35).J/2-(generalMeanRows 35).error (generalMeanGrid j.val)+
      (generalMeanRows 35).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 35).c)).2-
      (generalMeanRows 35).J/2-(generalMeanRows 35).error 4 := by
  have he : (generalMeanRows 35).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 35) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 35)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0035

/-! Kernel-checked entropy margins for general spectral rectangle 36. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0036
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6296163228, 6092700381, 5899095560, 5714741329, 5539074623, 5371572874, 5211750550, 5059156051, 4913368921, 4773997336, 4640675833, 4513063253, 4390840875, 4273710722, 4161394010, 4053629741, 3950173409, 3850795819, 3755282003, 3663430222, 3575051053, 3489966541, 3408009424, 3329022411, 3252857523, 3179375472, 3108445097, 3039942836, 2973752234, 2909763491, 2847873041, 2787983154, 2730001579, 2673841195, 2619419702, 2566659319, 2515486511, 2465831734, 2417629190, 2370816605, 2325335019, 2281128589, 2238144405, 2196332319, 2155644781, 2116036692, 2077465261, 2039889870, 2003271951, 1967574871, 1932763821, 1898805712, 1865669079, 1833323991, 1801741965, 1770895885, 1740759929, 1711309495, 1682521135, 1654372494, 1626842250, 1599910056, 1573556491, 1547763009, 1522511891, 1497786205, 1473569761, 1449847073, 1426603323, 1403824327, 1381496499, 1359606825, 1338142828, 1317092547, 1296444506, 1276187691, 1256311529, 1236805861, 1217660929, 1198867348, 1180416094, 1162298484, 1144506157, 1127031065, 1109865451, 1093001840, 1076433023, 1060152048, 1044152202, 1028427006, 1012970201, 997775739, 982837773, 968150648, 953708893, 939507212, 925540478, 911803724, 898292135, 885001044, 871925926, 859062388, 846406170, 833953131, 821699254, 809640631, 797773466, 786094068, 774598846, 763284306, 752147048, 741183759, 730391216, 719766274, 709305874, 699007027, 688866824, 678882423, 669051054, 659370012, 649836655]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 36).prefactor = (1123020520500103/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 36).cutoff/(generalMeanRows 36).c)).2 =
    (500901625680017/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 36).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 36).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 36).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 36

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 36).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 36).criticalRate j.val*(generalMeanRows 36).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 36).c*(generalMeanRows 36).criticalPoint j.val)).2-
      (generalMeanRows 36).J/2-(generalMeanRows 36).error (generalMeanGrid j.val)+
      (generalMeanRows 36).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 36).c)).2-
      (generalMeanRows 36).J/2-(generalMeanRows 36).error 4 := by
  have he : (generalMeanRows 36).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 36) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 36)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0036

/-! Kernel-checked entropy margins for general spectral rectangle 37. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0037
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6372405775, 6162312036, 5962409760, 5772072069, 5590717854, 5417807780, 5252840714, 5095350522, 4944903196, 4801094255, 4663546409, 4531907434, 4405848249, 4285061165, 4169258289, 4058170071, 3951543968, 3849143232, 3750745784, 3656143190, 3565139719, 3477551468, 3393205560, 3311939407, 3233600020, 3158043380, 3085133850, 3014743628, 2946752249, 2881046110, 2817518040, 2756066892, 2696597168, 2639018668, 2583246164, 2529199094, 2476801278, 2425980652, 2376669024, 2328801838, 2282317959, 2237159471, 2193271488, 2150601974, 2109101581, 2068723490, 2029423264, 1991158718, 1953889781, 1917578384, 1882188343, 1847685251, 1814036384, 1781210601, 1749178261, 1717911138, 1687382342, 1657566249, 1628438429, 1599975584, 1572155484, 1544956911, 1518359607, 1492344218, 1466892252, 1441986028, 1417608638, 1393743904, 1370376341, 1347491121, 1325074038, 1303111480, 1281590394, 1260498262, 1239823070, 1219553286, 1199677834, 1180186075, 1161067779, 1142313110, 1123912608, 1105857165, 1088138014, 1070746710, 1053675112, 1036915376, 1020459935, 1004301486, 988432983, 972847620, 957538822, 942500235, 927725716, 913209323, 898945306, 884928098, 871152311, 857612722, 844304272, 831222054, 818361310, 805717424, 793285915, 781062432, 769042750, 757222764, 745598483, 734166026, 722921622, 711861597, 700982380, 690280491, 679752543, 669395235, 659205352, 649179760, 639315403, 629609299, 620058541, 610660292, 601411783]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 37).prefactor = (5803389675077831/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 37).cutoff/(generalMeanRows 37).c)).2 =
    (49020633656327/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 37).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 37).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 37).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 37

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 37).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 37).criticalRate j.val*(generalMeanRows 37).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 37).c*(generalMeanRows 37).criticalPoint j.val)).2-
      (generalMeanRows 37).J/2-(generalMeanRows 37).error (generalMeanGrid j.val)+
      (generalMeanRows 37).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 37).c)).2-
      (generalMeanRows 37).J/2-(generalMeanRows 37).error 4 := by
  have he : (generalMeanRows 37).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 37) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 37)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0037

/-! Kernel-checked entropy margins for general spectral rectangle 38. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0038
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6066771017, 5851228202, 5646228751, 5451127884, 5265327804, 5088273585, 4919449506, 4758375759, 4604605499, 4457722180, 4317337150, 4183087476, 4054633967, 3931659378, 3813866774, 3700978041, 3592732512, 3488885727, 3389208277, 3293484758, 3201512799, 3113102172, 3028073967, 2946259835, 2867501288, 2791649045, 2718562437, 2648108845, 2580163187, 2514607439, 2451330184, 2390226203, 2331196089, 2274145884, 2218986747, 2165634645, 2114010056, 2064037700, 2015646287, 1968768278, 1923339663, 1879299755, 1836590994, 1795158768, 1754951239, 1715919187, 1678015858, 1641196827, 1605419862, 1570644803, 1536833448, 1503949439, 1471958163, 1440826659, 1410523520, 1381018814, 1352284001, 1324291862, 1297016423, 1270432889, 1244517586, 1219247897, 1194602209, 1170559858, 1147101083, 1124206975, 1101859438, 1080041142, 1058735490, 1037926575, 1017599149, 997738590, 978330866, 959362515, 940820606, 922692722, 904966930, 887631760, 870676180, 854089580, 837861746, 821982845, 806443408, 791234309, 776346753, 761772260, 747502650, 733530028, 719846774, 706445529, 693319185, 680460872, 667863950, 655521994, 643428793, 631578334, 619964795, 608582540, 597426109, 586490209, 575769711, 565259642, 554955177, 544851634, 534944470, 525229274, 515701762, 506357773, 497193262, 488204299, 479387063, 470737837, 462253005, 453929049, 445762547, 437750163, 429888654, 422174856, 414605691, 407178157, 399889329]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 38).prefactor = (5997990438465347/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 38).cutoff/(generalMeanRows 38).c)).2 =
    (448533640162701/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 38).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 38).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 38).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 38

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 38).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 38).criticalRate j.val*(generalMeanRows 38).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 38).c*(generalMeanRows 38).criticalPoint j.val)).2-
      (generalMeanRows 38).J/2-(generalMeanRows 38).error (generalMeanGrid j.val)+
      (generalMeanRows 38).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 38).c)).2-
      (generalMeanRows 38).J/2-(generalMeanRows 38).error 4 := by
  have he : (generalMeanRows 38).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 38) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 38)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0038

/-! Kernel-checked entropy margins for general spectral rectangle 39. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0039
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5465516978, 5248144697, 5041666813, 4845420292, 4658790213, 4481205564, 4312135481, 4151085877, 3997596425, 3851237823, 3711609342, 3578336592, 3451069504, 3329480492, 3213262780, 3102128877, 2995809178, 2894050688, 2796615850, 2703281468, 2613837719, 2528087241, 2445844292, 2366933975, 2291191523, 2218461633, 2148597855, 2081462023, 2016923725, 1954859816, 1895153959, 1837696206, 1782382602, 1729114815, 1677799800, 1628349475, 1580680426, 1534713628, 1490374187, 1447591095, 1406297005, 1366428017, 1327923481, 1290725809, 1254780302, 1220034986, 1186440459, 1153949744, 1122518160, 1092103189, 1062664360, 1034163137, 1006562812, 979828409, 953926589, 928825559, 904494998, 880905972, 858030862, 835843299, 814318095, 793431183, 773159560, 753481233, 734375164, 715821227, 697800159, 680293514, 663283631, 646753584, 630687156, 615068797, 599883596, 585117248, 570756024, 556786748, 543196765, 529973920, 517106533, 504583378, 492393662, 480527003, 468973414, 457723284, 446767359, 436096730, 425702813, 415577340, 405712339, 396100127, 386733293, 377604688, 368707414, 360034815, 351580461, 343338145, 335301872, 327465847, 319824471, 312372330, 305104190, 298014987, 291099824, 284353960, 277772806, 271351922, 265087004, 258973888, 253008535, 247187035, 241505596, 235960542, 230548311, 225265445, 220108591, 215074496, 210160005, 205362051, 200677662, 196103948, 191638106]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 39).prefactor = (1239823320995217/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 39).cutoff/(generalMeanRows 39).c)).2 =
    (379540768675747/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 39).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 39).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 39).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 39

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 39).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 39).criticalRate j.val*(generalMeanRows 39).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 39).c*(generalMeanRows 39).criticalPoint j.val)).2-
      (generalMeanRows 39).J/2-(generalMeanRows 39).error (generalMeanGrid j.val)+
      (generalMeanRows 39).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 39).c)).2-
      (generalMeanRows 39).J/2-(generalMeanRows 39).error 4 := by
  have he : (generalMeanRows 39).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 39) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 39)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0039

/-! Kernel-checked entropy margins for general spectral rectangle 40. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0040
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4964194725, 4747331601, 4541681217, 4346559830, 4161333154, 3985412044, 3818248632, 3659332869, 3508189418, 3364374859, 3227475157, 3097103383, 2972897629, 2854519134, 2741650558, 2633994417, 2531271654, 2433220321, 2339594384, 2250162611, 2164707563, 2083024653, 2004921286, 1930216065, 1858738049, 1790326082, 1724828151, 1662100812, 1602008642, 1544423736, 1489225243, 1436298925, 1385536756, 1336836543, 1290101575, 1245240293, 1202165985, 1160796500, 1121053979, 1082864609, 1046158382, 1010868883, 976933081, 944291137, 912886225, 882664363, 853574252, 825567131, 798596634, 772618660, 747591250, 723474469, 700230299, 677822534, 656216687, 635379895, 615280834, 595889642, 577177836, 559118247, 541684949, 524853195, 508599357, 492900869, 477736175, 463084676, 448926684, 435243373, 422016742, 409229569, 396865377, 384908394, 373343521, 362156301, 351332883, 340860000, 330724934, 320915497, 311420001, 302227237, 293326451, 284707327, 276359961, 268274847, 260442856, 252855222, 245503520, 238379658, 231475856, 224784637, 218298811, 212011461, 205915934, 200005830, 194274988, 188717477, 183327589, 178099824, 173028887, 168109675, 163337273, 158706942, 154214113, 149854385, 145623509, 141517390, 137532076, 133663755, 129908748, 126263503, 122724593, 119288706, 115952647, 112713329, 109567768, 106513083, 103546490, 100665297, 97866904, 95148796, 92508541]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 40).prefactor = (6406986986115087/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 40).cutoff/(generalMeanRows 40).c)).2 =
    (315002247538181/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 40).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 40).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 40).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 40

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 40).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 40).criticalRate j.val*(generalMeanRows 40).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 40).c*(generalMeanRows 40).criticalPoint j.val)).2-
      (generalMeanRows 40).J/2-(generalMeanRows 40).error (generalMeanGrid j.val)+
      (generalMeanRows 40).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 40).c)).2-
      (generalMeanRows 40).J/2-(generalMeanRows 40).error 4 := by
  have he : (generalMeanRows 40).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 40) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 40)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0040

/-! Kernel-checked entropy margins for general spectral rectangle 41. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0041
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5398606179, 5227258891, 5064295019, 4909178062, 4761412031, 4620537876, 4486130292, 4357794842, 4235165383, 4117901734, 4005687572, 3898228522, 3795250434, 3696497802, 3601732334, 3510731647, 3423288067, 3339207541, 3258308633, 3180421604, 3105387574, 3033057739, 2963292662, 2895961611, 2830941957, 2768118611, 2707383506, 2648635120, 2591778032, 2536722515, 2483384152, 2431683488, 2381545699, 2332900293, 2285680825, 2239824636, 2195272611, 2151968950, 2109860960, 2068898856, 2029035580, 1990226628, 1952429896, 1915605525, 1879715769, 1844724863, 1810598899, 1777305721, 1744814815, 1713097208, 1682125383, 1651873188, 1622315755, 1593429428, 1565191691, 1537581101, 1510577226, 1484160590, 1458312615, 1433015571, 1408252530, 1384007321, 1360264484, 1337009237, 1314227431, 1291905525, 1270030544, 1248590054, 1227572132, 1206965336, 1186758686, 1166941633, 1147504039, 1128436159, 1109728617, 1091372387, 1073358780, 1055679421, 1038326238, 1021291447, 1004567534, 988147248, 972023581, 956189764, 940639252, 925365712, 910363017, 895625236, 881146621, 866921604, 852944788, 839210935, 825714967, 812451951, 799417099, 786605759, 774013411, 761635658, 749468227, 737506959, 725747806, 714186828, 702820187, 691644144, 680655056, 669849371, 659223625, 648774440, 638498520, 628392648, 618453683, 608678559, 599064280, 589607921, 580306621, 571157586, 562158083, 553305441, 544597045, 536030339, 527602821]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 41).prefactor = (5183689353571203/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 41).cutoff/(generalMeanRows 41).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 41).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 41).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 41).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 41

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 41).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 41).criticalRate j.val*(generalMeanRows 41).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 41).c*(generalMeanRows 41).criticalPoint j.val)).2-
      (generalMeanRows 41).J/2-(generalMeanRows 41).error (generalMeanGrid j.val)+
      (generalMeanRows 41).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 41).c)).2-
      (generalMeanRows 41).J/2-(generalMeanRows 41).error 4 := by
  have he : (generalMeanRows 41).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 41) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 41)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0041

/-! Kernel-checked entropy margins for general spectral rectangle 42. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0042
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5539471414, 5363653181, 5196437110, 5037272703, 4885651029, 4741101061, 4603186394, 4471502302, 4345673086, 4225349690, 4110207535, 3999944569, 3894279485, 3792950111, 3695711939, 3602336780, 3512611545, 3426337115, 3343327320, 3263407994, 3186416110, 3112198980, 3040613530, 2971525618, 2904809413, 2840346825, 2778026965, 2717745664, 2659405010, 2602912936, 2548182821, 2495133137, 2443687109, 2393772403, 2345320843, 2298268133, 2252553617, 2208120039, 2164913330, 2122882406, 2081978981, 2042157392, 2003374434, 1965589209, 1928762986, 1892859065, 1857842656, 1823680763, 1790342075, 1757796864, 1726016895, 1694975332, 1664646661, 1635006606, 1606032065, 1577701035, 1549992551, 1522886628, 1496364205, 1470407088, 1444997908, 1420120071, 1395757716, 1371895671, 1348519423, 1325615073, 1303169311, 1281169377, 1259603036, 1238458550, 1217724650, 1197390512, 1177445736, 1157880320, 1138684643, 1119849447, 1101365812, 1083225147, 1065419170, 1047939892, 1030779604, 1013930865, 997386485, 981139518, 965183248, 949511177, 934117019, 918994686, 904138282, 889542094, 875200582, 861108373, 847260256, 833651170, 820276201, 807130577, 794209657, 781508934, 769024019, 756750647, 744684664, 732822026, 721158796, 709691138, 698415313, 687327676, 676424674, 665702840, 655158791, 644789228, 634590926, 624560741, 614695598, 604992495, 595448498, 586060738, 576826412, 567742778, 558807155, 550016919, 541369503]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 42).prefactor = (5318946788015599/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 42).cutoff/(generalMeanRows 42).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 42).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 42).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 42).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 42

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 42).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 42).criticalRate j.val*(generalMeanRows 42).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 42).c*(generalMeanRows 42).criticalPoint j.val)).2-
      (generalMeanRows 42).J/2-(generalMeanRows 42).error (generalMeanGrid j.val)+
      (generalMeanRows 42).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 42).c)).2-
      (generalMeanRows 42).J/2-(generalMeanRows 42).error 4 := by
  have he : (generalMeanRows 42).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 42) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 42)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0042

/-! Kernel-checked entropy margins for general spectral rectangle 43. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0043
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5684012231, 5503606392, 5332027170, 5168709704, 5013131783, 4864810088, 4723296829, 4588176718, 4459064255, 4335601273, 4217454727, 4104314681, 3995892490, 3891919140, 3792143742, 3696332157, 3604265730, 3515740151, 3430564391, 3348559739, 3269558914, 3193405245, 3119951923, 3049061308, 2980604285, 2914459681, 2850513716, 2788659501, 2728796572, 2670830456, 2614672274, 2560238371, 2507449967, 2456232842, 2406517041, 2358236590, 2311329250, 2265736271, 2221402174, 2178274542, 2136303829, 2095443180, 2055648262, 2016877111, 1979089985, 1942249228, 1906319140, 1871265864, 1837057273, 1803662864, 1771053664, 1739202137, 1708082102, 1677668653, 1647938083, 1618867814, 1590436336, 1562623141, 1535408671, 1508774258, 1482702079, 1457175108, 1432177068, 1407692394, 1383706191, 1360204201, 1337172764, 1314598788, 1292469719, 1270773512, 1249498605, 1228633891, 1208168697, 1188092763, 1168396216, 1149069555, 1130103629, 1111489622, 1093219035, 1075283672, 1057675623, 1040387251, 1023411180, 1006740283, 990367668, 974286668, 958490831, 942973913, 927729863, 912752818, 898037094, 883577179, 869367724, 855403538, 841679577, 828190946, 814932882, 801900760, 789090078, 776496458, 764115638, 751943470, 739975913, 728209031, 716638987, 705262042, 694074548, 683072950, 672253777, 661613642, 651149238, 640857336, 630734783, 620778498, 610985470, 601352756, 591877480, 582556828, 573388049, 564368450, 555495398]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 43).prefactor = (5457733479775513/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 43).cutoff/(generalMeanRows 43).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 43).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 43).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 43).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 43

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 43).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 43).criticalRate j.val*(generalMeanRows 43).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 43).c*(generalMeanRows 43).criticalPoint j.val)).2-
      (generalMeanRows 43).J/2-(generalMeanRows 43).error (generalMeanGrid j.val)+
      (generalMeanRows 43).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 43).c)).2-
      (generalMeanRows 43).J/2-(generalMeanRows 43).error 4 := by
  have he : (generalMeanRows 43).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 43) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 43)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0043

/-! Kernel-checked entropy margins for general spectral rectangle 44. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0044
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5757690856, 5574946518, 5401143213, 5235708755, 5078114165, 4927869861, 4784522246, 4647650649, 4516864574, 4391801212, 4272123199, 4157516583, 4047688976, 3942367879, 3841299150, 3744245613, 3650985782, 3561312696, 3475032851, 3391965219, 3311940350, 3234799545, 3160394090, 3088584559, 3019240167, 2952238168, 2887463308, 2824807312, 2764168413, 2705450915, 2648564787, 2593425288, 2539952618, 2488071595, 2437711355, 2388805073, 2341289699, 2295105725, 2250196950, 2206510279, 2163995523, 2122605221, 2082294464, 2043020745, 2004743806, 1967425502, 1931029673, 1895522022, 1860870004, 1827042722, 1794010827, 1761746427, 1730223001, 1699415320, 1669299369, 1639852279, 1611052259, 1582878538, 1555311302, 1528331642, 1501921505, 1476063642, 1450741566, 1425939511, 1401642389, 1377835756, 1354505776, 1331639186, 1309223270, 1287245828, 1265695146, 1244559974, 1223829502, 1203493335, 1183541473, 1163964291, 1144752521, 1125897231, 1107389813, 1089221964, 1071385672, 1053873200, 1036677079, 1019790086, 1003205242, 986915793, 970915204, 955197149, 939755499, 924584315, 909677839, 895030489, 880636845, 866491648, 852589792, 838926315, 825496395, 812295344, 799318605, 786561741, 774020436, 761690487, 749567801, 737648391, 725928371, 714403953, 703071443, 691927237, 680967821, 670189764, 659589716, 649164406, 638910640, 628825297, 618905328, 609147751, 599549652, 590108182, 580820553, 571684038, 562695970]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 44).prefactor = (1382119745419287/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 44).cutoff/(generalMeanRows 44).c)).2 =
    (107692945451133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 44).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 44).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 44).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 44

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 44).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 44).criticalRate j.val*(generalMeanRows 44).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 44).c*(generalMeanRows 44).criticalPoint j.val)).2-
      (generalMeanRows 44).J/2-(generalMeanRows 44).error (generalMeanGrid j.val)+
      (generalMeanRows 44).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 44).c)).2-
      (generalMeanRows 44).J/2-(generalMeanRows 44).error 4 := by
  have he : (generalMeanRows 44).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 44) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 44)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0044

/-! Kernel-checked entropy margins for general spectral rectangle 45. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0045
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7386863928, 7160149562, 6943957597, 6737673265, 6540725265, 6352581949, 6172747935, 6000761078, 5836189751, 5678630410, 5527705394, 5383060935, 5244365363, 5111307466, 4983595003, 4860953352, 4743124262, 4629864725, 4520945928, 4416152302, 4315280640, 4218139281, 4124547368, 4034334152, 3947338352, 3863407562, 3782397699, 3704172497, 3628603024, 3555567247, 3484949616, 3416640682, 3350536738, 3286539484, 3224555717, 3164497035, 3106279565, 3049823710, 2995053902, 2941898384, 2890288993, 2840160966, 2791452750, 2744105832, 2698064566, 2653276029, 2609689865, 2567258153, 2525935280, 2485677814, 2446444390, 2408195605, 2370893913, 2334503531, 2298990345, 2264321825, 2230466945, 2197396106, 2165081062, 2133494855, 2102611743, 2072407149, 2042857592, 2013940641, 1985634857, 1957919748, 1930775720, 1904184032, 1878126757, 1852586741, 1827547562, 1802993503, 1778909508, 1755281156, 1732094632, 1709336692, 1686994641, 1665056304, 1643510003, 1622344533, 1601549142, 1581113503, 1561027703, 1541282217, 1521867894, 1502775938, 1483997893, 1465525623, 1447351304, 1429467407, 1411866681, 1394542148, 1377487082, 1360695005, 1344159672, 1327875063, 1311835371, 1296034992, 1280468520, 1265130734, 1250016592, 1235121225, 1220439926, 1205968144, 1191701479, 1177635674, 1163766611, 1150090302, 1136602886, 1123300624, 1110179890, 1097237172, 1084469063, 1071872260, 1059443557, 1047179842, 1035078093, 1023135376, 1011348840, 999715715, 988233305]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 45).prefactor = (2773206945032943/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 45).cutoff/(generalMeanRows 45).c)).2 =
    (95469938913923/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 45).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 45).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 45).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 45

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 45).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 45).criticalRate j.val*(generalMeanRows 45).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 45).c*(generalMeanRows 45).criticalPoint j.val)).2-
      (generalMeanRows 45).J/2-(generalMeanRows 45).error (generalMeanGrid j.val)+
      (generalMeanRows 45).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 45).c)).2-
      (generalMeanRows 45).J/2-(generalMeanRows 45).error 4 := by
  have he : (generalMeanRows 45).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 45) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 45)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0045

/-! Kernel-checked entropy margins for general spectral rectangle 46. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0046
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7565767494, 7328599301, 7102432973, 6886626774, 6680584342, 6483750708, 6295608753, 6115676052, 5943502031, 5778665421, 5620771968, 5469452349, 5324360300, 5185170903, 5051579038, 4923297964, 4800058024, 4681605460, 4567701328, 4458120497, 4352650732, 4251091847, 4153254921, 4058961580, 3968043326, 3880340919, 3795703802, 3713989568, 3635063464, 3558797933, 3485072178, 3413771768, 3344788262, 3278018858, 3213366072, 3150737426, 3090045172, 3031206015, 2974140871, 2918774627, 2865035921, 2812856939, 2762173216, 2712923458, 2665049366, 2618495479, 2573209016, 2529139741, 2486239821, 2444463702, 2403767991, 2364111339, 2325454338, 2287759420, 2250990761, 2215114189, 2180097107, 2145908405, 2112518387, 2079898704, 2048022277, 2016863244, 1986396890, 1956599596, 1927448782, 1898922856, 1871001167, 1843663955, 1816892313, 1790668141, 1764974108, 1739793617, 1715110766, 1690910317, 1667177666, 1643898809, 1621060315, 1598649299, 1576653399, 1555060746, 1533859945, 1513040051, 1492590552, 1472501342, 1452762708, 1433365310, 1414300165, 1395558628, 1377132380, 1359013412, 1341194009, 1323666740, 1306424445, 1289460221, 1272767410, 1256339592, 1240170571, 1224254369, 1208585211, 1193157521, 1177965911, 1163005174, 1148270277, 1133756350, 1119458685, 1105372722, 1091494050, 1077818397, 1064341622, 1051059715, 1037968788, 1025065072, 1012344910, 999804754, 987441160, 975250785, 963230381, 951376794, 939686958, 928157891, 916786696]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 46).prefactor = (1450359956917193/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 46).cutoff/(generalMeanRows 46).c)).2 =
    (2325398009889/5000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 46).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 46).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 46).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 46

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 46).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 46).criticalRate j.val*(generalMeanRows 46).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 46).c*(generalMeanRows 46).criticalPoint j.val)).2-
      (generalMeanRows 46).J/2-(generalMeanRows 46).error (generalMeanGrid j.val)+
      (generalMeanRows 46).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 46).c)).2-
      (generalMeanRows 46).J/2-(generalMeanRows 46).error 4 := by
  have he : (generalMeanRows 46).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 46) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 46)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0046

/-! Kernel-checked entropy margins for general spectral rectangle 47. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0047
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7750640603, 7502655925, 7266175159, 7040528329, 6825092822, 6619289240, 6422577696, 6234454515, 6054449265, 5882122109, 5717061393, 5558881493, 5407220842, 5261740152, 5122120796, 4988063321, 4859286103, 4735524110, 4616527761, 4502061894, 4391904796, 4285847329, 4183692108, 4085252750, 3990353177, 3898826969, 3810516766, 3725273709, 3642956928, 3563433056, 3486575782, 3412265436, 3340388597, 3270837728, 3203510841, 3138311172, 3075146889, 3013930812, 2954580151, 2897016261, 2841164413, 2786953579, 2734316228, 2683188136, 2633508210, 2585218314, 2538263115, 2492589932, 2448148596, 2404891320, 2362772567, 2321748942, 2281779072, 2242823508, 2204844623, 2167806517, 2131674933, 2096417169, 2062002003, 2028399617, 1995581526, 1963520512, 1932190559, 1901566798, 1871625445, 1842343750, 1813699949, 1785673210, 1758243592, 1731392000, 1705100145, 1679350506, 1654126290, 1629411401, 1605190405, 1581448497, 1558171475, 1535345709, 1512958115, 1490996129, 1469447684, 1448301186, 1427545491, 1407169888, 1387164075, 1367518143, 1348222556, 1329268138, 1310646052, 1292347788, 1274365148, 1256690229, 1239315415, 1222233361, 1205436982, 1188919442, 1172674140, 1156694707, 1140974988, 1125509037, 1110291108, 1095315646, 1080577278, 1066070808, 1051791206, 1037733602, 1023893283, 1010265682, 996846375, 983631071, 970615613, 957795968, 945168223, 932728580, 920473353, 908398962, 896501929, 884778875, 873226515, 861841655, 850621190]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 47).prefactor = (6068191941885833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 47).cutoff/(generalMeanRows 47).c)).2 =
    (90591648289091/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 47).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 47).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 47).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 47

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 47).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 47).criticalRate j.val*(generalMeanRows 47).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 47).c*(generalMeanRows 47).criticalPoint j.val)).2-
      (generalMeanRows 47).J/2-(generalMeanRows 47).error (generalMeanGrid j.val)+
      (generalMeanRows 47).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 47).c)).2-
      (generalMeanRows 47).J/2-(generalMeanRows 47).error 4 := by
  have he : (generalMeanRows 47).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 47) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 47)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0047

/-! Kernel-checked entropy margins for general spectral rectangle 48. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0048
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6915530823, 6660543284, 6417562340, 6185894631, 5964895728, 5753965824, 5552545909, 5360114346, 5176183810, 5000298533, 4832031829, 4670983848, 4516779554, 4369066879, 4227515053, 4091813074, 3961668314, 3836805244, 3716964264, 3601900629, 3491383457, 3385194826, 3283128926, 3184991290, 3090598072, 2999775384, 2912358680, 2828192183, 2747128354, 2669027397, 2593756799, 2521190902, 2451210499, 2383702466, 2318559406, 2255679330, 2194965344, 2136325369, 2079671870, 2024921606, 1971995392, 1920817881, 1871317352, 1823425521, 1777077349, 1732210877, 1688767057, 1646689604, 1605924848, 1566421601, 1528131026, 1491006517, 1455003589, 1420079761, 1386194465, 1353308942, 1321386154, 1290390701, 1260288734, 1231047884, 1202637184, 1175027007, 1148188994, 1122095996, 1096722017, 1072042155, 1048032552, 1024670346, 1001933618, 979801354, 958253400, 937270420, 916833862, 896925916, 877529486, 858628153, 840206147, 822248314, 804740091, 787667478, 771017014, 754775751, 738931234, 723471477, 708384940, 693660517, 679287509, 665255611, 651554893, 638175787, 625109066, 612345834, 599877511, 587695818, 575792767, 564160647, 552792013, 541679675, 530816687, 520196339, 509812145, 499657835, 489727346, 480014815, 470514570, 461221121, 452129155, 443233530, 434529265, 426011536, 417675670, 409517138, 401531551, 393714653, 386062319, 378570546, 371235451, 364053269, 357020341, 350133120, 343388158]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 48).prefactor = (6347209406180287/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 48).cutoff/(generalMeanRows 48).c)).2 =
    (90234835681301/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 48).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 48).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 48).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 48

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 48).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 48).criticalRate j.val*(generalMeanRows 48).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 48).c*(generalMeanRows 48).criticalPoint j.val)).2-
      (generalMeanRows 48).J/2-(generalMeanRows 48).error (generalMeanGrid j.val)+
      (generalMeanRows 48).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 48).c)).2-
      (generalMeanRows 48).J/2-(generalMeanRows 48).error 4 := by
  have he : (generalMeanRows 48).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 48) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 48)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0048

/-! Kernel-checked entropy margins for general spectral rectangle 49. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0049
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6498888530, 6296969963, 6104601603, 5921208206, 5746255930, 5579248720, 5419725093, 5267255251, 5121438491, 4981900873, 4848293110, 4720288670, 4597582036, 4479887144, 4366935942, 4258477088, 4154274752, 4054107519, 3957767388, 3865058847, 3775798020, 3689811891, 3606937573, 3527021647, 3449919541, 3375494962, 3303619361, 3234171447, 3167036728, 3102107086, 3039280382, 2978460094, 2919554967, 2862478698, 2807149640, 2753490519, 2701428178, 2650893333, 2601820348, 2554147018, 2507814373, 2462766492, 2418950328, 2376315541, 2334814350, 2294401384, 2255033548, 2216669897, 2179271515, 2142801403, 2107224374, 2072506952, 2038617281, 2005525035, 1973201336, 1941618674, 1910750838, 1880572843, 1851060864, 1822192178, 1793945104, 1766298948, 1739233951, 1712731241, 1686772787, 1661341356, 1636420472, 1611994374, 1588047985, 1564566872, 1541537216, 1518945783, 1496779890, 1475027382, 1453676602, 1432716368, 1412135951, 1391925050, 1372073775, 1352572621, 1333412456, 1314584499, 1296080304, 1277891743, 1260010996, 1242430528, 1225143083, 1208141668, 1191419541, 1174970200, 1158787369, 1142864993, 1127197225, 1111778414, 1096603102, 1081666011, 1066962036, 1052486241, 1038233843, 1024200215, 1010380874, 996771476, 983367810, 970165791, 957161458, 944350967, 931730585, 919296686, 907045750, 894974354, 883079169, 871356961, 859804581, 848418964, 837197127, 826136166, 815233251, 804485623, 793890595, 783445544, 773147915]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 49).prefactor = (5347170257036201/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 49).cutoff/(generalMeanRows 49).c)).2 =
    (494470735349727/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 49).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 49).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 49).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 49

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 49).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 49).criticalRate j.val*(generalMeanRows 49).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 49).c*(generalMeanRows 49).criticalPoint j.val)).2-
      (generalMeanRows 49).J/2-(generalMeanRows 49).error (generalMeanGrid j.val)+
      (generalMeanRows 49).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 49).c)).2-
      (generalMeanRows 49).J/2-(generalMeanRows 49).error 4 := by
  have he : (generalMeanRows 49).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 49) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 49)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0049

/-! Kernel-checked entropy margins for general spectral rectangle 50. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0050
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6594304763, 6385191816, 6185973917, 5996056135, 5814886340, 5641951474, 5476774218, 5318910009, 5167944361, 5023490454, 4885186952, 4752696039, 4625701624, 4503907720, 4387036959, 4274829244, 4167040510, 4063441594, 3963817194, 3867964917, 3775694398, 3686826493, 3601192532, 3518633626, 3439000033, 3362150568, 3287952051, 3216278801, 3147012169, 3080040091, 3015256689, 2952561885, 2891861052, 2833064681, 2776088073, 2720851058, 2667277717, 2615296139, 2564838183, 2515839259, 2468238124, 2421976687, 2376999827, 2333255231, 2290693228, 2249266641, 2208930652, 2169642665, 2131362186, 2094050704, 2057671585, 2022189967, 1987572665, 1953788080, 1920806111, 1888598076, 1857136639, 1826395734, 1796350498, 1766977210, 1738253230, 1710156940, 1682667695, 1655765769, 1629432308, 1603649286, 1578399465, 1553666348, 1529434148, 1505687749, 1482412673, 1459595047, 1437221574, 1415279506, 1393756611, 1372641154, 1351921870, 1331587940, 1311628973, 1292034979, 1272796357, 1253903873, 1235348639, 1217122105, 1199216034, 1181622496, 1164333845, 1147342713, 1130641995, 1114224833, 1098084611, 1082214942, 1066609653, 1051262784, 1036168571, 1021321440, 1006716001, 992347037, 978209497, 964298490, 950609276, 937137264, 923878000, 910827165, 897980570, 885334147, 872883948, 860626137, 848556987, 836672878, 824970288, 813445791, 802096056, 790917840, 779907985, 769063418, 758381142, 747858239, 737491865, 727279244, 717217673]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 50).prefactor = (5539061945954633/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 50).cutoff/(generalMeanRows 50).c)).2 =
    (483541664817537/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 50).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 50).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 50).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 50

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 50).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 50).criticalRate j.val*(generalMeanRows 50).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 50).c*(generalMeanRows 50).criticalPoint j.val)).2-
      (generalMeanRows 50).J/2-(generalMeanRows 50).error (generalMeanGrid j.val)+
      (generalMeanRows 50).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 50).c)).2-
      (generalMeanRows 50).J/2-(generalMeanRows 50).error 4 := by
  have he : (generalMeanRows 50).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 50) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 50)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0050

/-! Kernel-checked entropy margins for general spectral rectangle 51. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0051
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6692246725, 6475774217, 6269554244, 6072971439, 5885454690, 5706473286, 5535533464, 5372175328, 5215970075, 5066517506, 4923443768, 4786399320, 4655057081, 4529110751, 4408273278, 4292275462, 4180864677, 4073803699, 3970869635, 3871852933, 3776556476, 3684794746, 3596393050, 3511186811, 3429020903, 3349749047, 3273233241, 3199343235, 3127956047, 3058955508, 2992231840, 2927681265, 2865205639, 2804712114, 2746112814, 2689324546, 2634268515, 2580870073, 2529058468, 2478766625, 2429930930, 2382491028, 2336389645, 2291572403, 2247987664, 2205586373, 2164321911, 2124149965, 2085028395, 2046917116, 2009777987, 1973574703, 1938272694, 1903839035, 1870242353, 1837452748, 1805441710, 1774182051, 1743647827, 1713814281, 1684657774, 1656155732, 1628286587, 1601029725, 1574365440, 1548274884, 1522740027, 1497743609, 1473269110, 1449300705, 1425823232, 1402822161, 1380283559, 1358194062, 1336540848, 1315311610, 1294494530, 1274078256, 1254051878, 1234404912, 1215127271, 1196209255, 1177641526, 1159415095, 1141521305, 1123951814, 1106698581, 1089753854, 1073110155, 1056760267, 1040697224, 1024914300, 1009404994, 994163028, 979182328, 964457022, 949981428, 935750047, 921757555, 907998794, 894468768, 881162634, 868075695, 855203396, 842541318, 830085170, 817830788, 805774126, 793911252, 782238346, 770751694, 759447682, 748322797, 737373617, 726596814, 715989144, 705547449, 695268652, 685149754, 675187832, 665380032]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 51).prefactor = (5737839972600481/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 51).cutoff/(generalMeanRows 51).c)).2 =
    (472730748713323/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 51).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 51).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 51).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 51

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 51).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 51).criticalRate j.val*(generalMeanRows 51).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 51).c*(generalMeanRows 51).criticalPoint j.val)).2-
      (generalMeanRows 51).J/2-(generalMeanRows 51).error (generalMeanGrid j.val)+
      (generalMeanRows 51).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 51).c)).2-
      (generalMeanRows 51).J/2-(generalMeanRows 51).error 4 := by
  have he : (generalMeanRows 51).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 51) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 51)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0051

/-! Kernel-checked entropy margins for general spectral rectangle 52. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0052
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5918914385, 5698677959, 5489074954, 5289473054, 5099285246, 4917965856, 4745007020, 4579935522, 4422309959, 4271718182, 4127774993, 3990120059, 3858416019, 3732346767, 3611615885, 3495945214, 3385073548, 3278755440, 3176760105, 3078870409, 2984881948, 2894602189, 2807849686, 2724453351, 2644251781, 2567092639, 2492832072, 2421334180, 2352470517, 2286119631, 2222166633, 2160502799, 2101025196, 2043636335, 1988243849, 1934760188, 1883102337, 1833191555, 1784953123, 1738316117, 1693213187, 1649580360, 1607356845, 1566484857, 1526909447, 1488578348, 1451441828, 1415452546, 1380565427, 1346737539, 1313927973, 1282097741, 1251209669, 1221228303, 1192119818, 1163851933, 1136393829, 1109716076, 1083790558, 1058590407, 1034089942, 1010264603, 987090899, 964546354, 942609452, 921259595, 900477053, 880242924, 860539092, 841348190, 822653562, 804439230, 786689862, 769390738, 752527726, 736087249, 720056265, 704422235, 689173106, 674297283, 659783613, 645621364, 631800200, 618310173, 605141696, 592285536, 579732788, 567474872, 555503508, 543810713, 532388778, 521230266, 510327994, 499675023, 489264650, 479090398, 469146005, 459425414, 449922769, 440632403, 431548832, 422666747, 413981007, 405486633, 397178802, 389052839, 381104215, 373328535, 365721540, 358279099, 350997200, 343871955, 336899586, 330076425, 323398912, 316863587, 310467091, 304206155, 298077608, 292078361, 286205415]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 52).prefactor = (5943751464129509/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 52).cutoff/(generalMeanRows 52).c)).2 =
    (97552431256329/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 52).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 52).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 52).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 52

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 52).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 52).criticalRate j.val*(generalMeanRows 52).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 52).c*(generalMeanRows 52).criticalPoint j.val)).2-
      (generalMeanRows 52).J/2-(generalMeanRows 52).error (generalMeanGrid j.val)+
      (generalMeanRows 52).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 52).c)).2-
      (generalMeanRows 52).J/2-(generalMeanRows 52).error 4 := by
  have he : (generalMeanRows 52).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 52) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 52)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0052

/-! Kernel-checked entropy margins for general spectral rectangle 53. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0053
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5199097063, 4979900200, 4771682057, 4573789780, 4385617087, 4206600200, 4036214219, 3873969870, 3719410595, 3572109928, 3431669125, 3297715023, 3169898100, 3047890711, 2931385478, 2820093826, 2713744642, 2612083052, 2514869289, 2421877667, 2332895624, 2247722850, 2166170478, 2088060337, 2013224263, 1941503461, 1872747912, 1806815823, 1743573119, 1682892969, 1624655344, 1568746606, 1515059127, 1463490933, 1413945367, 1366330785, 1320560257, 1276551304, 1234225634, 1193508915, 1154330543, 1116623437, 1080323843, 1045371148, 1011707710, 979278692, 948031915, 917917710, 888888785, 860900097, 833908735, 807873806, 782756329, 758519136, 735126776, 712545430, 690742823, 669688148, 649351991, 629706259, 610724115, 592379916, 574649151, 557508386, 540935212, 524908195, 509406825, 494411475, 479903357, 465864480, 452277616, 439126258, 426394591, 414067458, 402130326, 390569262, 379370900, 368522419, 358011516, 347826382, 337955681, 328388527, 319114464, 310123449, 301405830, 292952331, 284754034, 276802364, 269089077, 261606238, 254346215, 247301664, 240465514, 233830958, 227391441, 221140649, 215072501, 209181136, 203460906, 197906366, 192512269, 187273551, 182185332, 177242902, 172441717, 167777391, 163245693, 158842537, 154563977, 150406204, 146365538, 142438423, 138621425, 134911225, 131304614, 127798491, 124389857, 121075812, 117853553, 114720367, 111673629]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 53).prefactor = (6157052416247571/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 53).cutoff/(generalMeanRows 53).c)).2 =
    (304849876074161/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 53).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 53).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 53).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 53

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 53).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 53).criticalRate j.val*(generalMeanRows 53).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 53).c*(generalMeanRows 53).criticalPoint j.val)).2-
      (generalMeanRows 53).J/2-(generalMeanRows 53).error (generalMeanGrid j.val)+
      (generalMeanRows 53).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 53).c)).2-
      (generalMeanRows 53).J/2-(generalMeanRows 53).error 4 := by
  have he : (generalMeanRows 53).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 53) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 53)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0053

/-! Kernel-checked entropy margins for general spectral rectangle 54. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0054
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5518609194, 5345605764, 5180912384, 5024009723, 4874416952, 4731688374, 4595410405, 4465198867, 4340696552, 4221571030, 4107512661, 3998232802, 3893462169, 3792949359, 3696459498, 3603773001, 3514684450, 3429001562, 3346544235, 3267143688, 3190641653, 3116889647, 3045748291, 2977086684, 2910781828, 2846718094, 2784786728, 2724885397, 2666917761, 2610793084, 2556425872, 2503735527, 2452646043, 2403085704, 2354986820, 2308285469, 2262921263, 2218837128, 2175979101, 2134296135, 2093739924, 2054264736, 2015827255, 1978386439, 1941903381, 1906341184, 1871664842, 1837841128, 1804838488, 1772626948, 1741178017, 1710464607, 1680460946, 1651142509, 1622485944, 1594469007, 1567070497, 1540270202, 1514048839, 1488388009, 1463270140, 1438678449, 1414596898, 1391010147, 1367903527, 1345262994, 1323075103, 1301326973, 1280006258, 1259101118, 1238600194, 1218492583, 1198767816, 1179415833, 1160426963, 1141791905, 1123501713, 1105547770, 1087921781, 1070615751, 1053621973, 1036933015, 1020541704, 1004441116, 988624563, 973085583, 957817931, 942815565, 928072640, 913583497, 899342658, 885344814, 871584821, 858057690, 844758583, 831682804, 818825794, 806183128, 793750505, 781523744, 769498783, 757671669, 746038557, 734595705, 723339470, 712266302, 701372745, 690655431, 680111074, 669736473, 659528504, 649484119, 639600343, 629874274, 620303075, 610883977, 601614274, 592491322, 583512536, 574675390, 565977412]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 54).prefactor = (2512336626194057/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 54).cutoff/(generalMeanRows 54).c)).2 =
    (51990930898841/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 54).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 54).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 54).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 54

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 54).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 54).criticalRate j.val*(generalMeanRows 54).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 54).c*(generalMeanRows 54).criticalPoint j.val)).2-
      (generalMeanRows 54).J/2-(generalMeanRows 54).error (generalMeanGrid j.val)+
      (generalMeanRows 54).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 54).c)).2-
      (generalMeanRows 54).J/2-(generalMeanRows 54).error 4 := by
  have he : (generalMeanRows 54).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 54) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 54)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0054

/-! Kernel-checked entropy margins for general spectral rectangle 55. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0055
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5557769931, 5380101208, 5210980313, 5049874088, 4896288875, 4749767056, 4609883960, 4476245083, 4348483588, 4226258057, 4109250453, 3997164275, 3889722887, 3786667993, 3687758253, 3592768015, 3501486161, 3413715044, 3329269520, 3247976054, 3169671903, 3094204360, 3021430062, 2951214343, 2883430649, 2817959987, 2754690421, 2693516603, 2634339339, 2577065186, 2521606079, 2467878988, 2415805587, 2365311963, 2316328334, 2268788789, 2222631047, 2177796229, 2134228654, 2091875637, 2050687309, 2010616447, 1971618312, 1933650500, 1896672807, 1860647090, 1825537156, 1791308638, 1757928895, 1725366906, 1693593182, 1662579673, 1632299691, 1602727825, 1573839876, 1545612786, 1518024573, 1491054271, 1464681877, 1438888294, 1413655283, 1388965417, 1364802036, 1341149206, 1317991679, 1295314859, 1273104766, 1251348002, 1230031723, 1209143610, 1188671840, 1168605064, 1148932379, 1129643307, 1110727774, 1092176090, 1073978930, 1056127314, 1038612593, 1021426432, 1004560794, 988007926, 971760347, 955810833, 940152406, 924778325, 909682071, 894857338, 880298028, 865998233, 851952236, 838154496, 824599643, 811282470, 798197927, 785341113, 772707272, 760291782, 748090157, 736098036, 724311178, 712725462, 701336875, 690141515, 679135583, 668315379, 657677299, 647217833, 636933557, 626821137, 616877317, 607098924, 597482862, 588026109, 578725713, 569578793, 560582537, 551734193, 543031077, 534470563, 526050083]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 55).prefactor = (2582030757746247/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 55).cutoff/(generalMeanRows 55).c)).2 =
    (63786731286121/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 55).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 55).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 55).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 55

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 55).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 55).criticalRate j.val*(generalMeanRows 55).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 55).c*(generalMeanRows 55).criticalPoint j.val)).2-
      (generalMeanRows 55).J/2-(generalMeanRows 55).error (generalMeanGrid j.val)+
      (generalMeanRows 55).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 55).c)).2-
      (generalMeanRows 55).J/2-(generalMeanRows 55).error 4 := by
  have he : (generalMeanRows 55).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 55) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 55)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0055

/-! Kernel-checked entropy margins for general spectral rectangle 56. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0056
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5597911110, 5415517033, 5241915172, 5076558116, 4918938984, 4768587873, 4625068680, 4487976251, 4356933823, 4231590707, 4111620202, 3996717705, 3886598990, 3780998650, 3679668674, 3582377147, 3488907065, 3399055246, 3312631337, 3229456900, 3149364567, 3072197272, 2997807533, 2926056800, 2856814843, 2789959197, 2725374637, 2662952702, 2602591248, 2544194036, 2487670351, 2432934641, 2379906193, 2328508822, 2278670584, 2230323516, 2183403379, 2137849435, 2093604228, 2050613383, 2008825419, 1968191572, 1928665636, 1890203805, 1852764534, 1816308400, 1780797983, 1746197746, 1712473924, 1679594422, 1647528722, 1616247789, 1585723985, 1555930995, 1526843748, 1498438351, 1470692018, 1443583014, 1417090594, 1391194948, 1365877154, 1341119125, 1316903567, 1293213935, 1270034395, 1247349784, 1225145575, 1203407847, 1182123249, 1161278972, 1140862724, 1120862699, 1101267555, 1082066393, 1063248729, 1044804478, 1026723934, 1008997749, 991616917, 974572760, 957856908, 941461286, 925378103, 909599834, 894119211, 878929210, 864023042, 849394137, 835036141, 820942902, 807108462, 793527049, 780193071, 767101103, 754245886, 741622316, 729225438, 717050444, 705092661, 693347549, 681810695, 670477810, 659344719, 648407364, 637661791, 627104155, 616730708, 606537802, 596521880, 586679476, 577007211, 567501789, 558159997, 548978697, 539954828, 531085404, 522367506, 513798284, 505374957, 497094803, 488955167]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 56).prefactor = (331707282198849/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 56).cutoff/(generalMeanRows 56).c)).2 =
    (31298123048607/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 56).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 56).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 56).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 56

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 56).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 56).criticalRate j.val*(generalMeanRows 56).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 56).c*(generalMeanRows 56).criticalPoint j.val)).2-
      (generalMeanRows 56).J/2-(generalMeanRows 56).error (generalMeanGrid j.val)+
      (generalMeanRows 56).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 56).c)).2-
      (generalMeanRows 56).J/2-(generalMeanRows 56).error 4 := by
  have he : (generalMeanRows 56).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 56) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 56)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0056

/-! Kernel-checked entropy margins for general spectral rectangle 57. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0057
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5753201428, 5565747600, 5387329891, 5217385705, 5055394098, 4900872133, 4753371607, 4612476131, 4477798486, 4348978256, 4225679678, 4107589698, 3994416206, 3885886432, 3781745486, 3681755018, 3585692004, 3493347627, 3404526254, 3319044494, 3236730339, 3157422364, 3080968997, 3007227844, 2936065063, 2867354790, 2800978605, 2736825038, 2674789111, 2614771917, 2556680221, 2500426101, 2445926603, 2393103430, 2341882642, 2292194389, 2243972652, 2197155007, 2151682404, 2107498960, 2064551766, 2022790705, 1982168290, 1942639499, 1904161633, 1866694178, 1830198676, 1794638601, 1759979255, 1726187651, 1693232424, 1661083733, 1629713176, 1599093706, 1569199557, 1540006172, 1511490135, 1483629107, 1456401766, 1429787756, 1403767627, 1378322791, 1353435475, 1329088675, 1305266116, 1281952217, 1259132047, 1236791297, 1214916248, 1193493735, 1172511125, 1151956284, 1131817556, 1112083739, 1092744059, 1073788150, 1055206038, 1036988115, 1019125126, 1001608151, 984428588, 967578139, 951048796, 934832826, 918922759, 903311376, 887991699, 872956978, 858200680, 843716483, 829498265, 815540094, 801836221, 788381072, 775169241, 762195483, 749454707, 736941970, 724652469, 712581538, 700724643, 689077375, 677635444, 666394678, 655351015, 644500502, 633839288, 623363623, 613069851, 602954412, 593013830, 583244721, 573643780, 564207784, 554933587, 545818117, 536858378, 528051440, 519394443, 510884592, 502519155]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 57).prefactor = (2727272758836693/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 57).cutoff/(generalMeanRows 57).c)).2 =
    (31298123048607/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 57).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 57).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 57).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 57

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 57).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 57).criticalRate j.val*(generalMeanRows 57).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 57).c*(generalMeanRows 57).criticalPoint j.val)).2-
      (generalMeanRows 57).J/2-(generalMeanRows 57).error (generalMeanGrid j.val)+
      (generalMeanRows 57).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 57).c)).2-
      (generalMeanRows 57).J/2-(generalMeanRows 57).error 4 := by
  have he : (generalMeanRows 57).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 57) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 57)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0057

/-! Kernel-checked entropy margins for general spectral rectangle 58. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0058
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5912799617, 5720145678, 5536778526, 5362119958, 5195634581, 5036826058, 4885233756, 4740429732, 4602016026, 4469622225, 4342903251, 4221537365, 4105224354, 3993683882, 3886653986, 3783889706, 3685161831, 3590255751, 3498970405, 3411117317, 3326519704, 3245011665, 3166437424, 3090650635, 3017513744, 2946897396, 2878679885, 2812746649, 2748989798, 2687307681, 2627604478, 2569789825, 2513778470, 2459489942, 2406848250, 2355781607, 2306222162, 2258105760, 2211371713, 2165962587, 2121824004, 2078904460, 2037155148, 1996529798, 1956984527, 1918477697, 1880969781, 1844423243, 1808802420, 1774073411, 1740203981, 1707163461, 1674922661, 1643453783, 1612730348, 1582727116, 1553420023, 1524786108, 1496803461, 1469451157, 1442709210, 1416558515, 1390980806, 1365958607, 1341475193, 1317514548, 1294061329, 1271100830, 1248618950, 1226602161, 1205037476, 1183912428, 1163215037, 1142933789, 1123057611, 1103575851, 1084478257, 1065754955, 1047396433, 1029393524, 1011737386, 994419494, 977431614, 960765800, 944414376, 928369922, 912625265, 897173469, 882007820, 867121821, 852509179, 838163797, 824079768, 810251363, 796673026, 783339367, 770245152, 757385301, 744754880, 732349093, 720163279, 708192906, 696433567, 684880974, 673530951, 662379437, 651422473, 640656204, 630076876, 619680826, 609464486, 599424374, 589557095, 579859338, 570327867, 560959528, 551751238, 542699989, 533802840, 525056919, 516459420]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 58).prefactor = (1401464691208119/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 58).cutoff/(generalMeanRows 58).c)).2 =
    (31298123048607/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 58).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 58).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 58).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 58

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 58).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 58).criticalRate j.val*(generalMeanRows 58).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 58).c*(generalMeanRows 58).criticalPoint j.val)).2-
      (generalMeanRows 58).J/2-(generalMeanRows 58).error (generalMeanGrid j.val)+
      (generalMeanRows 58).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 58).c)).2-
      (generalMeanRows 58).J/2-(generalMeanRows 58).error 4 := by
  have he : (generalMeanRows 58).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 58) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 58)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0058

/-! Kernel-checked entropy margins for general spectral rectangle 59. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0059
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6076825182, 5878826876, 5690372979, 5510869250, 5339765441, 5176551450, 5020753862, 4871932863, 4729679456, 4593612950, 4463378695, 4338646026, 4219106404, 4104471714, 3994472728, 3888857689, 3787391027, 3689852180, 3596034509, 3505744309, 3418799894, 3335030761, 3254276810, 3176387637, 3101221874, 3028646574, 2958536658, 2890774383, 2825248869, 2761855643, 2700496227, 2641077752, 2583512600, 2527718066, 2473616054, 2421132783, 2370198521, 2320747334, 2272716849, 2226048038, 2180685018, 2136574853, 2093667383, 2051915055, 2011272768, 1971697729, 1933149315, 1895588949, 1858979976, 1823287559, 1788478565, 1754521476, 1721386291, 1689044443, 1657468716, 1626633172, 1596513077, 1567084836, 1538325929, 1510214852, 1482731062, 1455854927, 1429567673, 1403851339, 1378688736, 1354063405, 1329959576, 1306362135, 1283256591, 1260629039, 1238466134, 1216755061, 1195483508, 1174639643, 1154212085, 1134189886, 1114562510, 1095319809, 1076452008, 1057949684, 1039803752, 1022005448, 1004546311, 987418175, 970613150, 954123610, 937942185, 922061744, 906475389, 891176441, 876158433, 861415099, 846940369, 832728353, 818773343, 805069797, 791612339, 778395746, 765414948, 752665014, 740141157, 727838717, 715753165, 703880094, 692215213, 680754347, 669493428, 658428495, 647555688, 636871244, 626371495, 616052863, 605911858, 595945077, 586149196, 576520972, 567057238, 557754900, 548610938, 539622398, 530786397]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 59).prefactor = (1440342389179181/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 59).cutoff/(generalMeanRows 59).c)).2 =
    (31298123048607/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 59).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 59).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 59).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 59

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 59).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 59).criticalRate j.val*(generalMeanRows 59).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 59).c*(generalMeanRows 59).criticalPoint j.val)).2-
      (generalMeanRows 59).J/2-(generalMeanRows 59).error (generalMeanGrid j.val)+
      (generalMeanRows 59).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 59).c)).2-
      (generalMeanRows 59).J/2-(generalMeanRows 59).error 4 := by
  have he : (generalMeanRows 59).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 59) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 59)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0059

/-! Kernel-checked entropy margins for general spectral rectangle 60. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0060
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7810652818, 7572364891, 7344833644, 7127445772, 6919630936, 6720857977, 6530631546, 6348489106, 6173998239, 6006754238, 5846377935, 5692513740, 5544827868, 5403006730, 5266755471, 5135796634, 5009868945, 4888726199, 4772136237, 4659880012, 4551750721, 4447553015, 4347102262, 4250223875, 4156752677, 4066532327, 3979414779, 3895259779, 3813934404, 3735312624, 3659274902, 3585707818, 3514503714, 3445560369, 3378780690, 3314072427, 3251347900, 3190523753, 3131520709, 3074263357, 3018679936, 2964702144, 2912264953, 2861306431, 2811767586, 2763592207, 2716726722, 2671120061, 2626723526, 2583490669, 2541377181, 2500340781, 2460341113, 2421339651, 2383299608, 2346185846, 2309964800, 2274604395, 2240073976, 2206344238, 2173387159, 2141175940, 2109684944, 2078889641, 2048766554, 2019293211, 1990448095, 1962210598, 1934560981, 1907480331, 1880950523, 1854954183, 1829474652, 1804495955, 1780002768, 1755980388, 1732414705, 1709292173, 1686599787, 1664325059, 1642455989, 1620981049, 1599889159, 1579169668, 1558812333, 1538807303, 1519145101, 1499816606, 1480813039, 1462125947, 1443747189, 1425668923, 1407883592, 1390383913, 1373162864, 1356213672, 1339529805, 1323104959, 1306933050, 1291008203, 1275324746, 1259877200, 1244660269, 1229668834, 1214897948, 1200342824, 1185998833, 1171861494, 1157926471, 1144189564, 1130646707, 1117293960, 1104127503, 1091143635, 1078338766, 1065709415, 1053252204, 1040963853, 1028841180, 1016881093, 1005080589]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 60).prefactor = (2809046487230661/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 60).cutoff/(generalMeanRows 60).c)).2 =
    (224975360190751/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 60).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 60).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 60).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 60

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 60).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 60).criticalRate j.val*(generalMeanRows 60).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 60).c*(generalMeanRows 60).criticalPoint j.val)).2-
      (generalMeanRows 60).J/2-(generalMeanRows 60).error (generalMeanGrid j.val)+
      (generalMeanRows 60).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 60).c)).2-
      (generalMeanRows 60).J/2-(generalMeanRows 60).error 4 := by
  have he : (generalMeanRows 60).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 60) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 60)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0060

/-! Kernel-checked entropy margins for general spectral rectangle 61. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0061
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8034135346, 7783994821, 7545142549, 7316935881, 7098777192, 6890109912, 6690414991, 6499207758, 6316035099, 6140472929, 5972123920, 5810615440, 5655597701, 5506742067, 5363739526, 5226299288, 5094147512, 4967026140, 4844691823, 4726914941, 4613478702, 4504178303, 4398820168, 4297221235, 4199208300, 4104617410, 4013293294, 3925088845, 3839864630, 3757488434, 3677834840, 3600784837, 3526225447, 3454049383, 3384154733, 3316444649, 3250827075, 3187214478, 3125523600, 3065675230, 3007593979, 2951208082, 2896449200, 2843252241, 2791555189, 2741298943, 2692427163, 2644886134, 2598624624, 2553593759, 2509746906, 2467039555, 2425429217, 2384875318, 2345339106, 2306783562, 2269173309, 2232474538, 2196654925, 2161683564, 2127530893, 2094168634, 2061569726, 2029708270, 1998559473, 1968099594, 1938305896, 1909156597, 1880630825, 1852708577, 1825370675, 1798598733, 1772375113, 1746682898, 1721505854, 1696828398, 1672635573, 1648913014, 1625646925, 1602824053, 1580431659, 1558457501, 1536889807, 1515717259, 1494928967, 1474514454, 1454463636, 1434766807, 1415414618, 1396398066, 1377708478, 1359337494, 1341277055, 1323519392, 1306057012, 1288882683, 1271989431, 1255370519, 1239019445, 1222929930, 1207095905, 1191511508, 1176171070, 1161069111, 1146200330, 1131559601, 1117141959, 1102942601, 1088956875, 1075180275, 1061608437, 1048237129, 1035062251, 1022079825, 1009285993, 996677013, 984249252, 971999183, 959923381, 948018520, 936281367]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 61).prefactor = (5897929619421179/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 61).cutoff/(generalMeanRows 61).c)).2 =
    (218840313894843/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 61).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 61).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 61).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 61

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 61).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 61).criticalRate j.val*(generalMeanRows 61).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 61).c*(generalMeanRows 61).criticalPoint j.val)).2-
      (generalMeanRows 61).J/2-(generalMeanRows 61).error (generalMeanGrid j.val)+
      (generalMeanRows 61).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 61).c)).2-
      (generalMeanRows 61).J/2-(generalMeanRows 61).error 4 := by
  have he : (generalMeanRows 61).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 61) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 61)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0061

/-! Kernel-checked entropy margins for general spectral rectangle 62. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0062
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7355388482, 7095914162, 6848269914, 6611787453, 6385845261, 6169864457, 5963305114, 5765662992, 5576466597, 5395274559, 5221673259, 5055274694, 4895714547, 4742650436, 4595760314, 4454741026, 4319306982, 4189188945, 4064132919, 3943899135, 3828261109, 3717004783, 3609927727, 3506838404, 3407555488, 3311907240, 3219730916, 3130872231, 3045184852, 2962529928, 2882775655, 2805796869, 2731474662, 2659696032, 2590353546, 2523345034, 2458573295, 2395945823, 2335374556, 2276775632, 2220069167, 2165179041, 2112032697, 2060560959, 2010697854, 1962380441, 1915548663, 1870145194, 1826115300, 1783406710, 1741969492, 1701755935, 1662720438, 1624819408, 1588011158, 1552255815, 1517515235, 1483752912, 1450933905, 1419024762, 1387993447, 1357809272, 1328442836, 1299865964, 1272051647, 1244973990, 1218608159, 1192930333, 1167917655, 1143548191, 1119800885, 1096655522, 1074092687, 1052093729, 1030640732, 1009716472, 989304398, 969388594, 949953751, 930985147, 912468615, 894390520, 876737737, 859497631, 842658031, 826207214, 810133883, 794427154, 779076531, 764071897, 749403493, 735061905, 721038051, 707323166, 693908786, 680786741, 667949139, 655388359, 643097035, 631068046, 619294514, 607769782, 596487417, 585441192, 574625086, 564033267, 553660093, 543500100, 533547995, 523798654, 514247108, 504888546, 495718299, 486731845, 477924797, 469292898, 460832021, 452538158, 444407420, 436436032, 428620328]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 62).prefactor = (1238340979893839/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 62).cutoff/(generalMeanRows 62).c)).2 =
    (355763505321799/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 62).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 62).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 62).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 62

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 62).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 62).criticalRate j.val*(generalMeanRows 62).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 62).c*(generalMeanRows 62).criticalPoint j.val)).2-
      (generalMeanRows 62).J/2-(generalMeanRows 62).error (generalMeanGrid j.val)+
      (generalMeanRows 62).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 62).c)).2-
      (generalMeanRows 62).J/2-(generalMeanRows 62).error 4 := by
  have he : (generalMeanRows 62).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 62) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 62)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0062

/-! Kernel-checked entropy margins for general spectral rectangle 63. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0063
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6630363848, 6424516478, 6228174876, 6040780755, 5861815485, 5690796630, 5527274860, 5370831194, 5221074522, 5077639375, 4940183919, 4808388134, 4681952169, 4560594844, 4444052286, 4332076684, 4224435155, 4120908701, 4021291251, 3925388790, 3833018541, 3744008232, 3658195399, 3575426756, 3495557608, 3418451305, 3343978736, 3272017866, 3202453295, 3135175856, 3070082236, 3007074629, 2946060405, 2886951804, 2829665653, 2774123097, 2720249352, 2667973468, 2617228115, 2567949371, 2520076540, 2473551961, 2428320846, 2384331121, 2341533271, 2299880208, 2259327130, 2219831407, 2181352456, 2143851633, 2107292135, 2071638894, 2036858492, 2002919069, 1969790247, 1937443047, 1905849821, 1874984180, 1844820931, 1815336016, 1786506452, 1758310277, 1730726503, 1703735058, 1677316749, 1651453211, 1626126871, 1601320906, 1577019206, 1553206341, 1529867524, 1506988584, 1484555933, 1462556538, 1440977898, 1419808011, 1399035360, 1378648879, 1358637943, 1338992338, 1319702245, 1300758223, 1282151191, 1263872409, 1245913464, 1228266255, 1210922980, 1193876118, 1177118422, 1160642902, 1144442817, 1128511661, 1112843154, 1097431234, 1082270042, 1067353920, 1052677395, 1038235178, 1024022153, 1010033366, 996264025, 982709489, 969365263, 956226990, 943290447, 930551541, 918006299, 905650869, 893481511, 881494592, 869686586, 858054067, 846593702, 835302255, 824176576, 813213602, 802410351, 791763923, 781271490, 770930302, 760737676]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 63).prefactor = (1312181102727523/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 63).cutoff/(generalMeanRows 63).c)).2 =
    (233535880580807/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 63).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 63).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 63).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 63

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 63).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 63).criticalRate j.val*(generalMeanRows 63).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 63).c*(generalMeanRows 63).criticalPoint j.val)).2-
      (generalMeanRows 63).J/2-(generalMeanRows 63).error (generalMeanGrid j.val)+
      (generalMeanRows 63).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 63).c)).2-
      (generalMeanRows 63).J/2-(generalMeanRows 63).error 4 := by
  have he : (generalMeanRows 63).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 63) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 63)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0063

/-! Kernel-checked entropy margins for general spectral rectangle 64. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0064
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6748627765, 6534942249, 6331130491, 6136613564, 5950853656, 5773350471, 5603638035, 5441281830, 5285876229, 5137042182, 4994425135, 4857693146, 4726535173, 4600659527, 4479792456, 4363676852, 4252071082, 4144747896, 4041493447, 3942106378, 3846396981, 3754186431, 3665306070, 3579596752, 3496908231, 3417098602, 3340033770, 3265586976, 3193638335, 3124074425, 3056787891, 2991677082, 2928645717, 2867602561, 2808461134, 2751139432, 2695559672, 2641648047, 2589334500, 2538552513, 2489238907, 2441333656, 2394779711, 2349522835, 2305511453, 2262696500, 2221031288, 2180471379, 2140974460, 2102500234, 2065010307, 2028468095, 1992838718, 1958088922, 1924186985, 1891102642, 1858807010, 1827272511, 1796472814, 1766382763, 1736978323, 1708236519, 1680135387, 1652653918, 1625772016, 1599470445, 1573730797, 1548535439, 1523867485, 1499710753, 1476049735, 1452869560, 1430155967, 1407895274, 1386074350, 1364680589, 1343701886, 1323126611, 1302943590, 1283142079, 1263711750, 1244642666, 1225925265, 1207550345, 1189509043, 1171792825, 1154393465, 1137303037, 1120513897, 1104018672, 1087810250, 1071881764, 1056226587, 1040838314, 1025710761, 1010837949, 996214096, 981833612, 967691088, 953781289, 940099147, 926639753, 913398350, 900370332, 887551229, 874936709, 862522568, 850304729, 838279230, 826442228, 814789988, 803318881, 792025381, 780906059, 769957578, 759176697, 748560256, 738105183, 727808486, 717667250, 707678635]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 64).prefactor = (1090172128875227/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 64).cutoff/(generalMeanRows 64).c)).2 =
    (456142690629423/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 64).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 64).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 64).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 64

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 64).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 64).criticalRate j.val*(generalMeanRows 64).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 64).c*(generalMeanRows 64).criticalPoint j.val)).2-
      (generalMeanRows 64).J/2-(generalMeanRows 64).error (generalMeanGrid j.val)+
      (generalMeanRows 64).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 64).c)).2-
      (generalMeanRows 64).J/2-(generalMeanRows 64).error 4 := by
  have he : (generalMeanRows 64).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 64) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 64)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0064

/-! Kernel-checked entropy margins for general spectral rectangle 65. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0065
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6870176117, 6648443524, 6436967118, 6235146499, 6042423891, 5858280415, 5682232773, 5513830274, 5352652177, 5198305292, 5050421820, 4908657399, 4772689336, 4642214992, 4516950320, 4396628531, 4280998864, 4169825478, 4062886414, 3959972663, 3860887289, 3765444636, 3673469586, 3584796878, 3499270479, 3416742998, 3337075145, 3260135227, 3185798682, 3113947644, 3044470540, 2977261708, 2912221053, 2849253712, 2788269754, 2729183887, 2671915196, 2616386889, 2562526065, 2510263491, 2459533399, 2410273290, 2362423755, 2315928302, 2270733198, 2226787319, 2184042006, 2142450934, 2101969984, 2062557131, 2024172326, 1986777395, 1950335941, 1914813248, 1880176198, 1846393182, 1813434027, 1781269920, 1749873341, 1719217991, 1689278739, 1660031554, 1631453457, 1603522463, 1576217535, 1549518536, 1523406183, 1497862007, 1472868312, 1448408139, 1424465227, 1401023982, 1378069444, 1355587258, 1333563642, 1311985362, 1290839707, 1270114461, 1249797885, 1229878689, 1210346015, 1191189417, 1172398838, 1153964599, 1135877375, 1118128183, 1100708367, 1083609580, 1066823773, 1050343181, 1034160310, 1018267925, 1002659041, 987326909, 972265007, 957467031, 942926886, 928638673, 914596688, 900795407, 887229483, 873893736, 860783148, 847892853, 835218138, 822754427, 810497284, 798442403, 786585605, 774922830, 763450136, 752163692, 741059776, 730134766, 719385144, 708807484, 698398454, 688154811, 678073398, 668151138, 658385036]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 65).prefactor = (1132156289350949/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 65).cutoff/(generalMeanRows 65).c)).2 =
    (445331774525207/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 65).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 65).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 65).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 65

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 65).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 65).criticalRate j.val*(generalMeanRows 65).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 65).c*(generalMeanRows 65).criticalPoint j.val)).2-
      (generalMeanRows 65).J/2-(generalMeanRows 65).error (generalMeanGrid j.val)+
      (generalMeanRows 65).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 65).c)).2-
      (generalMeanRows 65).J/2-(generalMeanRows 65).error 4 := by
  have he : (generalMeanRows 65).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 65) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 65)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0065

/-! Kernel-checked entropy margins for general spectral rectangle 66. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0066
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5900215532, 5675895776, 5462236325, 5258618670, 5064468005, 4879249407, 4702464429, 4533648050, 4372365944, 4218212023, 4070806221, 3929792492, 3794836991, 3665626432, 3541866579, 3423280886, 3309609240, 3200606818, 3096043038, 2995700594, 2899374567, 2806871612, 2718009198, 2632614916, 2550525832, 2471587893, 2395655371, 2322590349, 2252262247, 2184547378, 2119328532, 2056494594, 1995940185, 1937565324, 1881275123, 1826979484, 1774592837, 1724033874, 1675225316, 1628093688, 1582569104, 1538585076, 1496078322, 1454988596, 1415258525, 1376833450, 1339661289, 1303692393, 1268879422, 1235177225, 1202542724, 1170934807, 1140314227, 1110643508, 1081886853, 1054010059, 1026980440, 1000766745, 975339094, 950668903, 926728825, 903492686, 880935431, 859033066, 837762611, 817102046, 797030271, 777527058, 758573010, 740149523, 722238750, 704823563, 687887521, 671414839, 655390355, 639799505, 624628296, 609863274, 595491509, 581500562, 567878473, 554613729, 541695255, 529112386, 516854854, 504912770, 493276606, 481937181, 470885647, 460113472, 449612428, 439374580, 429392271, 419658113, 410164972, 400905963, 391874434, 383063963, 374468341, 366081571, 357897854, 349911584, 342117339, 334509875, 327084119, 319835160, 312758245, 305848774, 299102291, 292514481, 286081163, 279798287, 273661927, 267668278, 261813650, 256094467, 250507258, 245048657, 239715397, 234504311, 229412320]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 66).prefactor = (5878786613446863/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 66).cutoff/(generalMeanRows 66).c)).2 =
    (171601139724413/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 66).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 66).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 66).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 66

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 66).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 66).criticalRate j.val*(generalMeanRows 66).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 66).c*(generalMeanRows 66).criticalPoint j.val)).2-
      (generalMeanRows 66).J/2-(generalMeanRows 66).error (generalMeanGrid j.val)+
      (generalMeanRows 66).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 66).c)).2-
      (generalMeanRows 66).J/2-(generalMeanRows 66).error 4 := by
  have he : (generalMeanRows 66).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 66) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 66)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0066

/-! Kernel-checked entropy margins for general spectral rectangle 67. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0067
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5613876334, 5440433830, 5275160015, 5117556073, 4967159571, 4823541285, 4686302364, 4555071785, 4429504063, 4309277194, 4194090789, 4083664391, 3977735940, 3876060384, 3778408411, 3684565288, 3594329804, 3507513303, 3423938788, 3343440111, 3265861217, 3191055455, 3118884936, 3049219948, 2981938409, 2916925364, 2854072520, 2793277811, 2734445002, 2677483309, 2622307061, 2568835374, 2516991854, 2466704316, 2417904527, 2370527962, 2324513580, 2279803611, 2236343362, 2194081030, 2152967532, 2112956346, 2074003357, 2036066717, 1999106715, 1963085652, 1927967725, 1893718919, 1860306906, 1827700946, 1795871803, 1764791654, 1734434015, 1704773666, 1675786579, 1647449853, 1619741654, 1592641155, 1566128483, 1540184664, 1514791580, 1489931920, 1465589136, 1441747406, 1418391594, 1395507214, 1373080395, 1351097852, 1329546854, 1308415195, 1287691170, 1267363546, 1247421540, 1227854797, 1208653368, 1189807689, 1171308565, 1153147148, 1135314923, 1117803691, 1100605552, 1083712895, 1067118380, 1050814929, 1034795711, 1019054129, 1003583814, 988378613, 973432576, 958739950, 944295170, 930092850, 916127774, 902394890, 888889303, 875606269, 862541186, 849689589, 837047146, 824609650, 812373017, 800333276, 788486571, 776829150, 765357366, 754067669, 742956604, 732020809, 721257007, 710662008, 700232703, 689966059, 679859121, 669909006, 660112901, 650468060, 640971804, 631621516, 622414640, 613348678, 604421190]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 67).prefactor = (4847530771447951/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 67).cutoff/(generalMeanRows 67).c)).2 =
    (502219148927257/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 67).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 67).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 67).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 67

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 67).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 67).criticalRate j.val*(generalMeanRows 67).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 67).c*(generalMeanRows 67).criticalPoint j.val)).2-
      (generalMeanRows 67).J/2-(generalMeanRows 67).error (generalMeanGrid j.val)+
      (generalMeanRows 67).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 67).c)).2-
      (generalMeanRows 67).J/2-(generalMeanRows 67).error 4 := by
  have he : (generalMeanRows 67).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 67) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 67)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0067

/-! Kernel-checked entropy margins for general spectral rectangle 68. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0068
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5665741066, 5487268490, 5317212617, 5155060461, 5000336430, 4852599068, 4711438130, 4576471971, 4447345195, 4323726534, 4205306937, 4091797833, 3982929561, 3878449937, 3778122953, 3681727585, 3589056703, 3499916081, 3414123478, 3331507799, 3251908325, 3175174000, 3101162776, 3029741008, 2960782897, 2894169967, 2829790591, 2767539545, 2707317596, 2649031122, 2592591752, 2537916042, 2484925161, 2433544610, 2383703954, 2335336570, 2288379421, 2242772835, 2198460305, 2155388299, 2113506083, 2072765559, 2033121107, 1994529441, 1956949474, 1920342193, 1884670535, 1849899281, 1815994949, 1782925693, 1750661217, 1719172682, 1688432629, 1658414901, 1629094572, 1600447879, 1572452157, 1545085782, 1518328115, 1492159444, 1466560942, 1441514614, 1417003255, 1393010409, 1369520328, 1346517939, 1323988802, 1301919085, 1280295529, 1259105418, 1238336554, 1217977229, 1198016201, 1178442671, 1159246261, 1140416993, 1121945270, 1103821857, 1086037864, 1068584728, 1051454199, 1034638325, 1018129437, 1001920138, 986003286, 970371988, 955019584, 939939638, 925125929, 910572439, 896273348, 882223020, 868415998, 854846998, 841510898, 828402732, 815517685, 802851085, 790398400, 778155226, 766117290, 754280438, 742640634, 731193953, 719936578, 708864797, 697974996, 687263658, 676727358, 666362758, 656166607, 646135737, 636267059, 626557560, 617004300, 607604413, 598355099, 589253626, 580297326, 571483593, 562809881]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 68).prefactor = (998150374603673/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 68).cutoff/(generalMeanRows 68).c)).2 =
    (246255167400149/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 68).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 68).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 68).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 68

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 68).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 68).criticalRate j.val*(generalMeanRows 68).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 68).c*(generalMeanRows 68).criticalPoint j.val)).2-
      (generalMeanRows 68).J/2-(generalMeanRows 68).error (generalMeanGrid j.val)+
      (generalMeanRows 68).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 68).c)).2-
      (generalMeanRows 68).J/2-(generalMeanRows 68).error 4 := by
  have he : (generalMeanRows 68).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 68) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 68)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0068

/-! Kernel-checked entropy margins for general spectral rectangle 69. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0069
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5718823777, 5535242063, 5360332490, 5193567446, 5034457758, 4882549334, 4737420166, 4598677641, 4465956122, 4338914773, 4217235592, 4100621626, 3988795357, 3881497230, 3778484315, 3679529081, 3584418284, 3492951935, 3404942368, 3320213374, 3238599407, 3159944857, 3084103371, 3010937238, 2940316808, 2872119963, 2806231628, 2742543307, 2680952670, 2621363152, 2563683591, 2507827890, 2453714699, 2401267123, 2350412445, 2301081877, 2253210312, 2206736111, 2161600889, 2117749327, 2075128983, 2033690127, 1993385584, 1954170581, 1916002609, 1878841295, 1842648276, 1807387089, 1773023057, 1739523196, 1706856113, 1674991922, 1643902157, 1613559696, 1583938687, 1555014476, 1526763545, 1499163450, 1472192761, 1445831009, 1420058636, 1394856945, 1370208057, 1346094863, 1322500990, 1299410759, 1276809152, 1254681774, 1233014825, 1211795069, 1191009803, 1170646834, 1150694452, 1131141406, 1111976879, 1093190473, 1074772182, 1056712377, 1039001787, 1021631480, 1004592852, 987877604, 971477735, 955385524, 939593520, 924094525, 908881588, 893947990, 879287236, 864893042, 850759330, 836880217, 823250004, 809863172, 796714372, 783798421, 771110290, 758645100, 746398119, 734364751, 722540533, 710921130, 699502328, 688280031, 677250258, 666409133, 655752887, 645277851, 634980453, 624857213, 614904742, 605119737, 595498979, 586039329, 576737726, 567591184, 558596788, 549751695, 541053129, 532498379, 524084797]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 69).prefactor = (1027640893163281/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 69).cutoff/(generalMeanRows 69).c)).2 =
    (482894876100857/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 69).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 69).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 69).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 69

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 69).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 69).criticalRate j.val*(generalMeanRows 69).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 69).c*(generalMeanRows 69).criticalPoint j.val)).2-
      (generalMeanRows 69).J/2-(generalMeanRows 69).error (generalMeanGrid j.val)+
      (generalMeanRows 69).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 69).c)).2-
      (generalMeanRows 69).J/2-(generalMeanRows 69).error 4 := by
  have he : (generalMeanRows 69).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 69) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 69)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0069

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock00 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 0 i) := by
  fin_cases i
  · exact EntropyRow0000.numerical
  · exact EntropyRow0001.numerical
  · exact EntropyRow0002.numerical
  · exact EntropyRow0003.numerical
  · exact EntropyRow0004.numerical
  · exact EntropyRow0005.numerical
  · exact EntropyRow0006.numerical
  · exact EntropyRow0007.numerical
  · exact EntropyRow0008.numerical
  · exact EntropyRow0009.numerical
  · exact EntropyRow0010.numerical
  · exact EntropyRow0011.numerical
  · exact EntropyRow0012.numerical
  · exact EntropyRow0013.numerical
  · exact EntropyRow0014.numerical
  · exact EntropyRow0015.numerical
  · exact EntropyRow0016.numerical
  · exact EntropyRow0017.numerical
  · exact EntropyRow0018.numerical
  · exact EntropyRow0019.numerical
  · exact EntropyRow0020.numerical
  · exact EntropyRow0021.numerical
  · exact EntropyRow0022.numerical
  · exact EntropyRow0023.numerical
  · exact EntropyRow0024.numerical
  · exact EntropyRow0025.numerical
  · exact EntropyRow0026.numerical
  · exact EntropyRow0027.numerical
  · exact EntropyRow0028.numerical
  · exact EntropyRow0029.numerical
  · exact EntropyRow0030.numerical
  · exact EntropyRow0031.numerical
  · exact EntropyRow0032.numerical
  · exact EntropyRow0033.numerical
  · exact EntropyRow0034.numerical
  · exact EntropyRow0035.numerical
  · exact EntropyRow0036.numerical
  · exact EntropyRow0037.numerical
  · exact EntropyRow0038.numerical
  · exact EntropyRow0039.numerical
  · exact EntropyRow0040.numerical
  · exact EntropyRow0041.numerical
  · exact EntropyRow0042.numerical
  · exact EntropyRow0043.numerical
  · exact EntropyRow0044.numerical
  · exact EntropyRow0045.numerical
  · exact EntropyRow0046.numerical
  · exact EntropyRow0047.numerical
  · exact EntropyRow0048.numerical
  · exact EntropyRow0049.numerical
  · exact EntropyRow0050.numerical
  · exact EntropyRow0051.numerical
  · exact EntropyRow0052.numerical
  · exact EntropyRow0053.numerical
  · exact EntropyRow0054.numerical
  · exact EntropyRow0055.numerical
  · exact EntropyRow0056.numerical
  · exact EntropyRow0057.numerical
  · exact EntropyRow0058.numerical
  · exact EntropyRow0059.numerical
  · exact EntropyRow0060.numerical
  · exact EntropyRow0061.numerical
  · exact EntropyRow0062.numerical
  · exact EntropyRow0063.numerical
  · exact EntropyRow0064.numerical
  · exact EntropyRow0065.numerical
  · exact EntropyRow0066.numerical
  · exact EntropyRow0067.numerical
  · exact EntropyRow0068.numerical
  · exact EntropyRow0069.numerical
end SingularValueBounds.KL.Certificates
