import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 1260. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1260
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4606706777, 4477381629, 4352418067, 4231608328, 4114759962, 4001694231, 3892244720, 3786256124, 3683583182, 3584089741, 3487647929, 3394137428, 3303444825, 3215463035, 3130090793, 3047232190, 2966796266, 2888696637, 2812851168, 2739181666, 2667613613, 2598075916, 2530500687, 2464823033, 2400980871, 2338914760, 2278567741, 2219885191, 2162814695, 2107305921, 2053310504, 2000781946, 1949675514, 1899948154, 1851558403, 1804466312, 1758633375, 1714022454, 1670597725, 1628324606, 1587169713, 1547100797, 1508086699, 1470097303, 1433103491, 1397077100, 1361990885, 1327818480, 1294534365, 1262113829, 1230532940, 1199768517, 1169798097, 1140599911, 1112152859, 1084436483, 1057430943, 1031116997, 1005475978, 980489777, 956140817, 932412040, 909286887, 886749282, 864783615, 843374725, 822507888, 802168800, 782343565, 763018682, 744181028, 725817853, 707916763, 690465708, 673452977, 656867181, 640697246, 624932404, 609562183, 594576395, 579965134, 565718761, 551827899, 538283425, 525076462, 512198372, 499640749, 487395413, 475454401, 463809963, 452454556, 441380836, 430581654, 420050051, 409779249, 399762652, 389993833, 380466537, 371174672, 362112304, 353273655, 344653097, 336245149, 328044471, 320045862, 312244256, 304634718, 297212439, 289972736, 282911044, 276022919, 269304026, 262750146, 256357165, 250121075, 244037970, 238104045, 232315591, 226668992, 221160727, 215787361]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1260).prefactor = (259696115473323/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1260).cutoff/(generalMeanRows 1260).c)).2 =
    (68583946722501/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1260).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1260).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1260).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1260

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1260).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1260).criticalRate j.val*(generalMeanRows 1260).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1260).c*(generalMeanRows 1260).criticalPoint j.val)).2-
      (generalMeanRows 1260).J/2-(generalMeanRows 1260).error (generalMeanGrid j.val)+
      (generalMeanRows 1260).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1260).c)).2-
      (generalMeanRows 1260).J/2-(generalMeanRows 1260).error 4 := by
  have he : (generalMeanRows 1260).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1260) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1260)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1260

/-! Kernel-checked entropy margins for general spectral rectangle 1261. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1261
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5050748953, 4915985784, 4785624738, 4659456635, 4537287919, 4418939017, 4304242902, 4193043849, 4085196333, 3980564073, 3879019178, 3780441404, 3684717484, 3591740542, 3501409567, 3413628945, 3328308035, 3245360798, 3164705451, 3086264168, 3009962795, 2935730607, 2863500074, 2793206656, 2724788615, 2658186838, 2593344681, 2530207822, 2468724130, 2408843534, 2350517919, 2293701013, 2238348290, 2184416883, 2131865496, 2080654329, 2030745000, 1982100481, 1934685033, 1888464145, 1843404479, 1799473817, 1756641010, 1714875937, 1674149454, 1634433359, 1595700347, 1557923979, 1521078643, 1485139524, 1450082571, 1415884467, 1382522603, 1349975050, 1318220533, 1287238408, 1257008639, 1227511776, 1198728934, 1170641773, 1143232477, 1116483743, 1090378753, 1064901167, 1040035101, 1015765115, 992076198, 968953751, 946383580, 924351874, 902845203, 881850497, 861355042, 841346463, 821812717, 802742084, 784123152, 765944812, 748196250, 730866932, 713946605, 697425278, 681293223, 665540965, 650159271, 635139148, 620471834, 606148790, 592161697, 578502448, 565163140, 552136072, 539413738, 526988820, 514854186, 503002883, 491428129, 480123317, 469082000, 458297893, 447764870, 437476953, 427428315, 417613270, 408026275, 398661923, 389514938, 380580176, 371852617, 363327366, 354999646, 346864795, 338918269, 331155630, 323572551, 316164807, 308928278, 301858942, 294952875, 288206247, 281615320]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1261).prefactor = (171247932004741/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1261).cutoff/(generalMeanRows 1261).c)).2 =
    (223468762853337/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1261).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1261).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1261).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1261

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1261).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1261).criticalRate j.val*(generalMeanRows 1261).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1261).c*(generalMeanRows 1261).criticalPoint j.val)).2-
      (generalMeanRows 1261).J/2-(generalMeanRows 1261).error (generalMeanGrid j.val)+
      (generalMeanRows 1261).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1261).c)).2-
      (generalMeanRows 1261).J/2-(generalMeanRows 1261).error 4 := by
  have he : (generalMeanRows 1261).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1261) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1261)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1261

/-! Kernel-checked entropy margins for general spectral rectangle 1262. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1262
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5271702797, 5133979542, 5000698087, 4871647416, 4746632367, 4625471956, 4507997920, 4394053445, 4283492050, 4176176606, 4071978480, 3970776763, 3872457607, 3776913614, 3684043310, 3593750668, 3505944677, 3420538965, 3337451449, 3256604030, 3177922309, 3101335333, 3026775363, 2954177669, 2883480330, 2814624067, 2747552077, 2682209887, 2618545221, 2556507869, 2496049582, 2437123953, 2379686331, 2323693719, 2269104697, 2215879336, 2163979131, 2113366927, 2064006859, 2015864288, 1968905747, 1923098889, 1878412434, 1834816126, 1792280688, 1750777779, 1710279956, 1670760639, 1632194075, 1594555301, 1557820120, 1521965068, 1486967382, 1452804982, 1419456438, 1386900950, 1355118322, 1324088945, 1293793772, 1264214299, 1235332546, 1207131042, 1179592804, 1152701321, 1126440540, 1100794849, 1075749064, 1051288415, 1027398531, 1004065429, 981275502, 959015504, 937272544, 916034071, 895287864, 875022024, 855224962, 835885391, 816992318, 798535032, 780503099, 762886353, 745674887, 728859047, 712429424, 696376848, 680692380, 665367305, 650393128, 635761567, 621464545, 607494188, 593842815, 580502938, 567467253, 554728634, 542280133, 530114971, 518226536, 506608376, 495254196, 484157857, 473313366, 462714875, 452356681, 442233215, 432339043, 422668862, 413217497, 403979896, 394951129, 386126381, 377500956, 369070267, 360829836, 352775292, 344902368, 337206898, 329684813, 322332143, 315145008]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1262).prefactor = (4358662973475683/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1262).cutoff/(generalMeanRows 1262).c)).2 =
    (225091489808171/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1262).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1262).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1262).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1262

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1262).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1262).criticalRate j.val*(generalMeanRows 1262).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1262).c*(generalMeanRows 1262).criticalPoint j.val)).2-
      (generalMeanRows 1262).J/2-(generalMeanRows 1262).error (generalMeanGrid j.val)+
      (generalMeanRows 1262).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1262).c)).2-
      (generalMeanRows 1262).J/2-(generalMeanRows 1262).error 4 := by
  have he : (generalMeanRows 1262).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1262) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1262)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1262

/-! Kernel-checked entropy margins for general spectral rectangle 1263. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1263
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5755108037, 5594671831, 5439710030, 5289950921, 5145143724, 5005056384, 4869473634, 4738195312, 4611034869, 4487818062, 4368381808, 4252573155, 4140248385, 4031272208, 3925517049, 3822862410, 3723194300, 3626404725, 3532391227, 3441056474, 3352307884, 3266057291, 3182220639, 3100717706, 3021471851, 2944409785, 2869461359, 2796559376, 2725639416, 2656639667, 2589500783, 2524165747, 2460579740, 2398690026, 2338445845, 2279798311, 2222700315, 2167106443, 2112972893, 2060257396, 2008919147, 1958918741, 1910218105, 1862780443, 1816570179, 1771552907, 1727695341, 1684965266, 1643331500, 1602763848, 1563233065, 1524710816, 1487169647, 1450582944, 1414924909, 1380170522, 1346295519, 1313276362, 1281090209, 1249714899, 1219128917, 1189311379, 1160242007, 1131901111, 1104269566, 1077328794, 1051060747, 1025447888, 1000473176, 976120049, 952372408, 929214601, 906631415, 884608054, 863130132, 842183655, 821755015, 801830975, 782398655, 763445527, 744959400, 726928410, 709341015, 692185979, 675452366, 659129534, 643207120, 627675038, 612523468, 597742848, 583323869, 569257464, 555534806, 542147298, 529086564, 516344451, 503913014, 491784514, 479951415, 468406373, 457142234, 446152028, 435428964, 424966426, 414757966, 404797301, 395078310, 385595025, 376341633, 367312467, 358502004, 349904861, 341515791, 333329680, 325341544, 317546522, 309939877, 302516992, 295273365, 288204607, 281306439]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1263).prefactor = (651334832719799/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1263).cutoff/(generalMeanRows 1263).c)).2 =
    (494945733859273/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1263).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1263).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1263).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1263

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1263).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1263).criticalRate j.val*(generalMeanRows 1263).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1263).c*(generalMeanRows 1263).criticalPoint j.val)).2-
      (generalMeanRows 1263).J/2-(generalMeanRows 1263).error (generalMeanGrid j.val)+
      (generalMeanRows 1263).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1263).c)).2-
      (generalMeanRows 1263).J/2-(generalMeanRows 1263).error 4 := by
  have he : (generalMeanRows 1263).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1263) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1263)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1263

/-! Kernel-checked entropy margins for general spectral rectangle 1264. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1264
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5565821237, 5421963998, 5282716949, 5147861065, 5017193821, 4890527454, 4767687433, 4648511141, 4532846705, 4420551982, 4311493653, 4205546435, 4102592374, 4002520223, 3905224884, 3810606913, 3718572077, 3629030951, 3541898566, 3457094080, 3374540490, 3294164365, 3215895606, 3139667230, 3065415167, 2993078079, 2922597195, 2853916155, 2786980871, 2721739399, 2658141815, 2596140109, 2535688079, 2476741239, 2419256730, 2363193237, 2308510913, 2255171311, 2203137309, 2152373060, 2102843921, 2054516409, 2007358141, 1961337793, 1916425050, 1872590564, 1829805914, 1788043569, 1747276851, 1707479900, 1668627643, 1630695764, 1593660674, 1557499482, 1522189973, 1487710579, 1454040358, 1421158970, 1389046657, 1357684221, 1327053005, 1297134875, 1267912202, 1239367844, 1211485131, 1184247848, 1157640223, 1131646909, 1106252971, 1081443877, 1057205480, 1033524007, 1010386051, 987778556, 965688807, 944104421, 923013336, 902403801, 882264367, 862583881, 843351472, 824556547, 806188780, 788238108, 770694720, 753549053, 736791781, 720413811, 704406279, 688760537, 673468153, 658520903, 643910764, 629629912, 615670711, 602025716, 588687659, 575649451, 562904174, 550445078, 538265574, 526359235, 514719784, 503341099, 492217202, 481342258, 470710571, 460316582, 450154862, 440220113, 430507160, 421010952, 411726557, 402649159, 393774055, 385096653, 376612468, 368317121, 360206334, 352275931, 344521832]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1264).prefactor = (4544908671170569/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1264).cutoff/(generalMeanRows 1264).c)).2 =
    (141192385920063/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1264).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1264).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1264).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1264

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1264).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1264).criticalRate j.val*(generalMeanRows 1264).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1264).c*(generalMeanRows 1264).criticalPoint j.val)).2-
      (generalMeanRows 1264).J/2-(generalMeanRows 1264).error (generalMeanGrid j.val)+
      (generalMeanRows 1264).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1264).c)).2-
      (generalMeanRows 1264).J/2-(generalMeanRows 1264).error 4 := by
  have he : (generalMeanRows 1264).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1264) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1264)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1264

/-! Kernel-checked entropy margins for general spectral rectangle 1265. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1265
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6411957257, 6238700917, 6071244727, 5909300975, 5752604298, 5600909309, 5453988525, 5311630556, 5173638507, 5039828580, 4910028837, 4784078112, 4661825035, 4543127182, 4427850306, 4315867654, 4207059363, 4101311909, 3998517622, 3898574240, 3801384516, 3706855858, 3614900005, 3525432728, 3438373570, 3353645594, 3271175166, 3190891747, 3112727711, 3036618170, 2962500818, 2890315788, 2820005512, 2751514606, 2684789746, 2619779569, 2556434570, 2494707013, 2434550842, 2375921603, 2318776370, 2263073672, 2208773432, 2155836900, 2104226599, 2053906271, 2004840821, 1956996274, 1910339728, 1864839307, 1820464126, 1777184249, 1734970651, 1693795189, 1653630561, 1614450283, 1576228651, 1538940718, 1502562268, 1467069785, 1432440430, 1398652023, 1365683012, 1333512458, 1302120011, 1271485891, 1241590872, 1212416260, 1183943876, 1156156044, 1129035568, 1102565723, 1076730238, 1051513280, 1026899442, 1002873731, 979421555, 956528709, 934181363, 912366056, 891069679, 870279467, 849982991, 830168142, 810823131, 791936470, 773496972, 755493734, 737916137, 720753833, 703996739, 687635027, 671659123, 656059693, 640827641, 625954101, 611430428, 597248199, 583399199, 569875420, 556669056, 543772493, 531178308, 518879264, 506868302, 495138538, 483683260, 472495921, 461570135, 450899673, 440478461, 430300572, 420360226, 410651783, 401169744, 391908740, 382863536, 374029023, 365400218, 356972258, 348740396]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1265).prefactor = (5588760063486649/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1265).cutoff/(generalMeanRows 1265).c)).2 =
    (501080780155179/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1265).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1265).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1265).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1265

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1265).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1265).criticalRate j.val*(generalMeanRows 1265).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1265).c*(generalMeanRows 1265).criticalPoint j.val)).2-
      (generalMeanRows 1265).J/2-(generalMeanRows 1265).error (generalMeanGrid j.val)+
      (generalMeanRows 1265).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1265).c)).2-
      (generalMeanRows 1265).J/2-(generalMeanRows 1265).error 4 := by
  have he : (generalMeanRows 1265).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1265) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1265)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1265

/-! Kernel-checked entropy margins for general spectral rectangle 1266. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1266
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7075687059, 6894599159, 6719384842, 6549752389, 6385433070, 6226178688, 6071759425, 5921961964, 5776587837, 5635451979, 5498381442, 5365214271, 5235798503, 5109991275, 4987658045, 4868671878, 4752912825, 4640267361, 4530627876, 4423892228, 4319963330, 4218748788, 4120160561, 4024114663, 3930530890, 3839332569, 3750446331, 3663801902, 3579331916, 3496971741, 3416659314, 3338334999, 3261941451, 3187423488, 3114727975, 3043803720, 2974601373, 2907073332, 2841173657, 2776857991, 2714083486, 2652808730, 2592993682, 2534599612, 2477589044, 2421925697, 2367574442, 2314501244, 2262673126, 2212058121, 2162625231, 2114344393, 2067186439, 2021123063, 1976126790, 1932170943, 1889229612, 1847277631, 1806290549, 1766244602, 1727116694, 1688884370, 1651525795, 1615019736, 1579345535, 1544483099, 1510412872, 1477115827, 1444573441, 1412767683, 1381680998, 1351296293, 1321596919, 1292566661, 1264189726, 1236450724, 1209334662, 1182826929, 1156913288, 1131579859, 1106813116, 1082599870, 1058927265, 1035782765, 1013154144, 991029482, 969397152, 948245814, 927564406, 907342136, 887568478, 868233159, 849326158, 830837694, 812758225, 795078437, 777789239, 760881759, 744347338, 728177520, 712364054, 696898883, 681774141, 666982147, 652515404, 638366588, 624528550, 610994306, 597757038, 584810085, 572146943, 559761259, 547646828, 535797587, 524207616, 512871130, 501782479, 490936143, 480326728, 469948965, 459797707]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1266).prefactor = (5787967070728149/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1266).cutoff/(generalMeanRows 1266).c)).2 =
    (204590465995887/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1266).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1266).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1266).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1266

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1266).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1266).criticalRate j.val*(generalMeanRows 1266).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1266).c*(generalMeanRows 1266).criticalPoint j.val)).2-
      (generalMeanRows 1266).J/2-(generalMeanRows 1266).error (generalMeanGrid j.val)+
      (generalMeanRows 1266).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1266).c)).2-
      (generalMeanRows 1266).J/2-(generalMeanRows 1266).error 4 := by
  have he : (generalMeanRows 1266).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1266) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1266)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1266

/-! Kernel-checked entropy margins for general spectral rectangle 1267. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1267
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7726624716, 7542123302, 7363386935, 7190127690, 7022080760, 6859001951, 6700665507, 6546862201, 6397397663, 6252090911, 6110773057, 5973286165, 5839482237, 5709222321, 5582375712, 5458819243, 5338436656, 5221118029, 5106759276, 4995261688, 4886531526, 4780479649, 4677021182, 4576075214, 4477564524, 4381415331, 4287557071, 4195922185, 4106445935, 4019066227, 3933723455, 3850360356, 3768921872, 3689355030, 3611608825, 3535634117, 3461383532, 3388811367, 3317873515, 3248527376, 3180731791, 3114446970, 3049634429, 2986256932, 2924278431, 2863664017, 2804379869, 2746393209, 2689672256, 2634186186, 2579905093, 2526799954, 2474842591, 2424005641, 2374262523, 2325587409, 2277955198, 2231341486, 2185722543, 2141075289, 2097377271, 2054606638, 2012742126, 1971763034, 1931649207, 1892381017, 1853939344, 1816305565, 1779461531, 1743389558, 1708072409, 1673493281, 1639635791, 1606483965, 1574022224, 1542235371, 1511108585, 1480627402, 1450777713, 1421545745, 1392918061, 1364881542, 1337423382, 1310531080, 1284192429, 1258395508, 1233128679, 1208380573, 1184140084, 1160396367, 1137138824, 1114357103, 1092041088, 1070180894, 1048766863, 1027789554, 1007239741, 987108406, 967386734, 948066107, 929138102, 910594481, 892427192, 874628360, 857190286, 840105439, 823366455, 806966134, 790897429, 775153453, 759727465, 744612874, 729803229, 715292223, 701073683, 687141569, 673489974, 660113116, 647005338, 634161105, 621574999]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1267).prefactor = (1463983749141779/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1267).cutoff/(generalMeanRows 1267).c)).2 =
    (524242815992299/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1267).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1267).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1267).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1267

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1267).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1267).criticalRate j.val*(generalMeanRows 1267).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1267).c*(generalMeanRows 1267).criticalPoint j.val)).2-
      (generalMeanRows 1267).J/2-(generalMeanRows 1267).error (generalMeanGrid j.val)+
      (generalMeanRows 1267).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1267).c)).2-
      (generalMeanRows 1267).J/2-(generalMeanRows 1267).error 4 := by
  have he : (generalMeanRows 1267).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1267) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1267)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1267

/-! Kernel-checked entropy margins for general spectral rectangle 1268. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1268
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5179999930, 5027377795, 4880069582, 4737820938, 4600396023, 4467575598, 4339155363, 4214944498, 4094764386, 3978447491, 3865836365, 3756782769, 3651146896, 3548796680, 3449607174, 3353459996, 3260242838, 3169849014, 3082177063, 2997130377, 2914616880, 2834548722, 2756842010, 2681416557, 2608195654, 2537105863, 2468076825, 2401041082, 2335933916, 2272693198, 2211259247, 2151574706, 2093584418, 2037235315, 1982476316, 1929258229, 1877533660, 1827256929, 1778383991, 1730872361, 1684681043, 1639770468, 1596102425, 1553640011, 1512347570, 1472190641, 1433135914, 1395151177, 1358205275, 1322268069, 1287310393, 1253304021, 1220221625, 1188036746, 1156723761, 1126257846, 1096614957, 1067771791, 1039705767, 1012394996, 985818258, 959954979, 934785207, 910289591, 886449360, 863246308, 840662765, 818681589, 797286142, 776460278, 756188322, 736455059, 717245715, 698545946, 680341824, 662619822, 645366802, 628570002, 612217027, 596295834, 580794724, 565702328, 551007601, 536699808, 522768518, 509203593, 495995179, 483133696, 470609836, 458414546, 446539027, 434974724, 423713319, 412746725, 402067076, 391666725, 381538235, 371674373, 362068104, 352712586, 343601166, 334727369, 326084899, 317667631, 309469608, 301485031, 293708262, 286133815, 278756350, 271570674, 264571733, 257754610, 251114520, 244646805, 238346936, 232210502, 226233213, 220410891, 214739472, 209215001, 203833627]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1268).prefactor = (4971241770317151/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1268).cutoff/(generalMeanRows 1268).c)).2 =
    (1077734676171639/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1268).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1268).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1268).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1268

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1268).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1268).criticalRate j.val*(generalMeanRows 1268).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1268).c*(generalMeanRows 1268).criticalPoint j.val)).2-
      (generalMeanRows 1268).J/2-(generalMeanRows 1268).error (generalMeanGrid j.val)+
      (generalMeanRows 1268).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1268).c)).2-
      (generalMeanRows 1268).J/2-(generalMeanRows 1268).error 4 := by
  have he : (generalMeanRows 1268).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1268) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1268)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1268

/-! Kernel-checked entropy margins for general spectral rectangle 1269. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1269
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6042758408, 5881526623, 5725561574, 5574612997, 5428449321, 5286855702, 5149632308, 5016592828, 4887563155, 4762380242, 4640891079, 4522951803, 4408426902, 4297188508, 4189115773, 4084094300, 3982015648, 3882776877, 3786280145, 3692432335, 3601144733, 3512332720, 3425915505, 3341815870, 3259959952, 3180277027, 3102699326, 3027161860, 2953602254, 2881960608, 2812179353, 2744203129, 2677978667, 2613454679, 2550581759, 2489312289, 2429600350, 2371401640, 2314673400, 2259374342, 2205464580, 2152905566, 2101660038, 2051691954, 2002966448, 1955449779, 1909109278, 1863913314, 1819831246, 1776833383, 1734890950, 1693976051, 1654061638, 1615121472, 1577130101, 1540062827, 1503895678, 1468605384, 1434169351, 1400565635, 1367772924, 1335770514, 1304538285, 1274056687, 1244306718, 1215269903, 1186928284, 1159264395, 1132261252, 1105902335, 1080171572, 1055053331, 1030532396, 1006593964, 983223628, 960407362, 938131515, 916382797, 895148268, 874415328, 854171705, 834405451, 815104926, 796258792, 777856004, 759885803, 742337706, 725201496, 708467221, 692125180, 676165920, 660580227, 645359120, 630493844, 615975867, 601796867, 587948736, 574423563, 561213638, 548311443, 535709646, 523401096, 511378820, 499636019, 488166058, 476962468, 466018938, 455329314, 444887590, 434687908, 424724553, 414991950, 405484660, 396197374, 387124914, 378262227, 369604383, 361146570, 352884093, 344812371, 336926931]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1269).prefactor = (1280515388255433/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1269).cutoff/(generalMeanRows 1269).c)).2 =
    (223468762853337/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1269).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1269).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1269).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1269

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1269).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1269).criticalRate j.val*(generalMeanRows 1269).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1269).c*(generalMeanRows 1269).criticalPoint j.val)).2-
      (generalMeanRows 1269).J/2-(generalMeanRows 1269).error (generalMeanGrid j.val)+
      (generalMeanRows 1269).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1269).c)).2-
      (generalMeanRows 1269).J/2-(generalMeanRows 1269).error 4 := by
  have he : (generalMeanRows 1269).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1269) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1269)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1269

/-! Kernel-checked entropy margins for general spectral rectangle 1270. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1270
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7922034790, 7723812442, 7531939291, 7346099572, 7166002561, 6991379877, 6821983143, 6657581927, 6497961942, 6342923461, 6192279925, 6045856705, 5903490015, 5765025941, 5630319585, 5499234295, 5371640981, 5247417506, 5126448134, 5008623037, 4893837852, 4781993280, 4672994727, 4566751968, 4463178859, 4362193058, 4263715785, 4167671590, 4073988153, 3982596092, 3893428790, 3806422236, 3721514877, 3638647485, 3557763028, 3478806556, 3401725096, 3326467547, 3252984588, 3181228596, 3111153559, 3042715003, 2975869924, 2910576718, 2846795119, 2784486144, 2723612034, 2664136205, 2606023200, 2549238641, 2493749186, 2439522489, 2386527160, 2334732730, 2284109616, 2234629084, 2186263223, 2138984913, 2092767796, 2047586249, 2003415358, 1960230896, 1918009297, 1876727633, 1836363596, 1796895474, 1758302133, 1720562999, 1683658038, 1647567741, 1612273106, 1577755624, 1543997260, 1510980444, 1478688050, 1447103392, 1416210199, 1385992615, 1356435176, 1327522807, 1299240806, 1271574833, 1244510904, 1218035376, 1192134939, 1166796610, 1142007719, 1117755902, 1094029095, 1070815522, 1048103691, 1025882382, 1004140645, 982867788, 962053373, 941687207, 921759340, 902260053, 883179855, 864509478, 846239870, 828362187, 810867793, 793748252, 776995320, 760600947, 744557264, 728856585, 713491401, 698454372, 683738328, 669336261, 655241322, 641446818, 627946209, 614733100, 601801243, 589144530, 576756990, 564632787, 552766215]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1270).prefactor = (3158802862005693/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1270).cutoff/(generalMeanRows 1270).c)).2 =
    (1031391198625297/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1270).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1270).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1270).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1270

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1270).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1270).criticalRate j.val*(generalMeanRows 1270).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1270).c*(generalMeanRows 1270).criticalPoint j.val)).2-
      (generalMeanRows 1270).J/2-(generalMeanRows 1270).error (generalMeanGrid j.val)+
      (generalMeanRows 1270).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1270).c)).2-
      (generalMeanRows 1270).J/2-(generalMeanRows 1270).error 4 := by
  have he : (generalMeanRows 1270).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1270) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1270)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1270

/-! Kernel-checked entropy margins for general spectral rectangle 1271. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1271
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4702626235, 4565348831, 4432824336, 4304825117, 4181140179, 4061573444, 3945942253, 3834076052, 3725815240, 3621010158, 3519520195, 3421212997, 3325963766, 3233654637, 3144174118, 3057416596, 2973281891, 2891674848, 2812504985, 2735686156, 2661136262, 2588776978, 2518533510, 2450334373, 2384111181, 2319798467, 2257333509, 2196656167, 2137708746, 2080435855, 2024784285, 1970702893, 1918142498, 1867055776, 1817397170, 1769122808, 1722190412, 1676559235, 1632189977, 1589044731, 1547086913, 1506281203, 1466593497, 1427990846, 1390441414, 1353914427, 1318380131, 1283809753, 1250175456, 1217450308, 1185608241, 1154624022, 1124473220, 1095132172, 1066577959, 1038788378, 1011741911, 985417706, 959795550, 934855845, 910579589, 886948355, 863944269, 841549992, 819748701, 798524073, 777860269, 757741912, 738154080, 719082285, 700512460, 682430947, 664824483, 647680186, 630985544, 614728404, 598896960, 583479740, 568465599, 553843708, 539603541, 525734870, 512227755, 499072532, 486259810, 473780456, 461625594, 449786592, 438255060, 427022837, 416081987, 405424795, 395043755, 384931569, 375081137, 365485554, 356138103, 347032250, 338161639, 329520084, 321101570, 312900243, 304910407, 297126521, 289543191, 282155171, 274957352, 267944767, 261112577, 254456077, 247970685, 241651942, 235495508, 229497159, 223652783, 217958377, 212410045, 207003993, 201736531, 196604062, 191603087]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1271).prefactor = (4457252492064499/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1271).cutoff/(generalMeanRows 1271).c)).2 =
    (26865203975149/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1271).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1271).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1271).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1271

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1271).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1271).criticalRate j.val*(generalMeanRows 1271).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1271).c*(generalMeanRows 1271).criticalPoint j.val)).2-
      (generalMeanRows 1271).J/2-(generalMeanRows 1271).error (generalMeanGrid j.val)+
      (generalMeanRows 1271).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1271).c)).2-
      (generalMeanRows 1271).J/2-(generalMeanRows 1271).error 4 := by
  have he : (generalMeanRows 1271).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1271) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1271)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1271

/-! Kernel-checked entropy margins for general spectral rectangle 1272. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1272
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4705538997, 4568176565, 4435569986, 4307491485, 4183729938, 4064089144, 3948386333, 3836450842, 3728122975, 3623252978, 3521700153, 3423332064, 3328023837, 3235657532, 3146121589, 3059310331, 2975123513, 2893465924, 2814247024, 2737380614, 2662784544, 2590380442, 2520093466, 2451852087, 2385587877, 2321235329, 2258731680, 2198016755, 2139032822, 2081724457, 2026038417, 1971923528, 1919330577, 1868212212, 1818522849, 1770218586, 1723257121, 1677597679, 1633200940, 1590028971, 1548045164, 1507214180, 1467501891, 1428875330, 1391302640, 1354753028, 1319196723, 1284604932, 1250949803, 1218204385, 1186342595, 1155339186, 1125169708, 1095810486, 1067238588, 1039431794, 1012368575, 986028065, 960390038, 935434885, 911143593, 887497723, 864479388, 842071240, 820256445, 799018671, 778342068, 758211250, 738611286, 719527678, 700946351, 682853638, 665236269, 648081353, 631376371, 615109161, 599267911, 583841142, 568817701, 554186753, 539937766, 526060505, 512545024, 499381653, 486560995, 474073911, 461911520, 450065186, 438526511, 427287330, 416339704, 405675911, 395288441, 385169992, 375313459, 365711932, 356358692, 347247199, 338371093, 329724186, 321300457, 313094050, 305099266, 297310558, 289722532, 282329935, 275127658, 268110729, 261274308, 254613685, 248124276, 241801619, 235641372, 229639307, 223791311, 218093378, 212541609, 207132210, 201861484, 196725836, 191721764]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1272).prefactor = (2230006636059231/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1272).cutoff/(generalMeanRows 1272).c)).2 =
    (26865203975149/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1272).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1272).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1272).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1272

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1272).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1272).criticalRate j.val*(generalMeanRows 1272).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1272).c*(generalMeanRows 1272).criticalPoint j.val)).2-
      (generalMeanRows 1272).J/2-(generalMeanRows 1272).error (generalMeanGrid j.val)+
      (generalMeanRows 1272).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1272).c)).2-
      (generalMeanRows 1272).J/2-(generalMeanRows 1272).error 4 := by
  have he : (generalMeanRows 1272).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1272) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1272)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1272

/-! Kernel-checked entropy margins for general spectral rectangle 1273. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1273
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4979558242, 4844179521, 4713231141, 4586508917, 4463823159, 4344997203, 4229866126, 4118275630, 4010081053, 3905146503, 3803344090, 3704553248, 3608660129, 3515557063, 3425142077, 3337318459, 3251994373, 3169082503, 3088499736, 3010166877, 2934008382, 2859952124, 2787929171, 2717873593, 2649722271, 2583414736, 2518893012, 2456101473, 2394986715, 2335497430, 2277584295, 2221199868, 2166298493, 2112836204, 2060770645, 2010060992, 1960667874, 1912553312, 1865680648, 1820014487, 1775520641, 1732166074, 1689918852, 1648748098, 1608623944, 1569517491, 1531400767, 1494246693, 1458029043, 1422722415, 1388302193, 1354744523, 1322026278, 1290125037, 1259019051, 1228687227, 1199109098, 1170264800, 1142135057, 1114701154, 1087944918, 1061848704, 1036395370, 1011568268, 987351221, 963728507, 940684851, 918205403, 896275728, 874881791, 854009944, 833646918, 813779804, 794396047, 775483433, 757030080, 739024425, 721455218, 704311509, 687582642, 671258243, 655328215, 639782728, 624612211, 609807345, 595359055, 581258505, 567497088, 554066423, 540958344, 528164898, 515678338, 503491117, 491595880, 479985462, 468652884, 457591340, 446794203, 436255012, 425967470, 415925440, 406122941, 396554144, 387213364, 378095062, 369193837, 360504425, 352021691, 343740630, 335656365, 327764135, 320059303, 312537344, 305193846, 298024508, 291025134, 284191632, 277520012, 271006382, 264646946, 258438001]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1273).prefactor = (424147572261763/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1273).cutoff/(generalMeanRows 1273).c)).2 =
    (1227655288969521/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1273).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1273).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1273).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1273

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1273).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1273).criticalRate j.val*(generalMeanRows 1273).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1273).c*(generalMeanRows 1273).criticalPoint j.val)).2-
      (generalMeanRows 1273).J/2-(generalMeanRows 1273).error (generalMeanGrid j.val)+
      (generalMeanRows 1273).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1273).c)).2-
      (generalMeanRows 1273).J/2-(generalMeanRows 1273).error 4 := by
  have he : (generalMeanRows 1273).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1273) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1273)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1273

/-! Kernel-checked entropy margins for general spectral rectangle 1274. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1274
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5194958940, 5056548315, 4922610187, 4792938650, 4667342497, 4545643719, 4427676203, 4313284592, 4202323280, 4094655533, 3990152707, 3888693559, 3790163632, 3694454705, 3601464308, 3511095276, 3423255359, 3337856861, 3254816324, 3174054229, 3095494733, 3019065430, 2944697129, 2872323649, 2801881641, 2733310413, 2666551774, 2601549894, 2538251170, 2476604102, 2416559177, 2358068772, 2301087045, 2245569855, 2191474667, 2138760481, 2087387751, 2037318323, 1988515364, 1940943305, 1894567782, 1849355583, 1805274599, 1762293773, 1720383060, 1679513380, 1639656581, 1600785402, 1562873434, 1525895089, 1489825566, 1454640824, 1420317548, 1386833126, 1354165622, 1322293747, 1291196842, 1260854853, 1231248305, 1202358288, 1174166435, 1146654902, 1119806352, 1093603935, 1068031276, 1043072456, 1018711999, 994934854, 971726387, 949072363, 926958935, 905372631, 884300342, 863729315, 843647135, 824041721, 804901310, 786214453, 767970003, 750157105, 732765188, 715783959, 699203391, 683013719, 667205430, 651769255, 636696165, 621977362, 607604273, 593568545, 579862036, 566476811, 553405136, 540639472, 528172472, 515996970, 504105983, 492492702, 481150488, 470072866, 459253525, 448686309, 438365214, 428284386, 418438115, 408820831, 399427103, 390251632, 381289248, 372534911, 363983701, 355630819, 347471583, 339501427, 331715893, 324110633, 316681404, 309424065, 302334577, 295408996, 288643477]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1274).prefactor = (4318505616926999/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1274).cutoff/(generalMeanRows 1274).c)).2 =
    (308882336350107/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1274).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1274).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1274).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1274

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1274).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1274).criticalRate j.val*(generalMeanRows 1274).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1274).c*(generalMeanRows 1274).criticalPoint j.val)).2-
      (generalMeanRows 1274).J/2-(generalMeanRows 1274).error (generalMeanGrid j.val)+
      (generalMeanRows 1274).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1274).c)).2-
      (generalMeanRows 1274).J/2-(generalMeanRows 1274).error 4 := by
  have he : (generalMeanRows 1274).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1274) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1274)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1274

/-! Kernel-checked entropy margins for general spectral rectangle 1275. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1275
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5387347907, 5246741008, 5110620377, 4978779616, 4851027137, 4727184656, 4607085865, 4490575285, 4377507250, 4267745012, 4161159960, 4057630917, 3957043520, 3859289668, 3764267026, 3671878583, 3582032252, 3494640510, 3409620075, 3326891610, 3246379457, 3168011392, 3091718406, 3017434498, 2945096493, 2874643871, 2806018607, 2739165031, 2674029691, 2610561235, 2548710291, 2488429364, 2429672739, 2372396388, 2316557885, 2262116330, 2209032270, 2157267633, 2106785661, 2057550854, 2009528906, 1962686658, 1916992045, 1872414046, 1828922645, 1786488784, 1745084327, 1704682018, 1665255451, 1626779032, 1589227949, 1552578141, 1516806270, 1481889694, 1447806440, 1414535181, 1382055209, 1350346419, 1319389282, 1289164825, 1259654616, 1230840741, 1202705790, 1175232836, 1148405421, 1122207541, 1096623632, 1071638552, 1047237570, 1023406355, 1000130957, 977397802, 955193676, 933505715, 912321397, 891628524, 871415222, 851669924, 832381365, 813538569, 795130846, 777147778, 759579216, 742415269, 725646296, 709262903, 693255933, 677616458, 662335777, 647405405, 632817070, 618562706, 604634447, 591024624, 577725756, 564730546, 552031879, 539622813, 527496577, 515646564, 504066331, 492749591, 481690207, 470882195, 460319714, 449997065, 439908684, 430049144, 420413147, 410995524, 401791226, 392795329, 384003023, 375409617, 367010528, 358801282, 350777515, 342934963, 335269463, 327776953, 320453464]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1275).prefactor = (4370634514331987/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1275).cutoff/(generalMeanRows 1275).c)).2 =
    (248693178999233/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1275).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1275).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1275).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1275

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1275).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1275).criticalRate j.val*(generalMeanRows 1275).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1275).c*(generalMeanRows 1275).criticalPoint j.val)).2-
      (generalMeanRows 1275).J/2-(generalMeanRows 1275).error (generalMeanGrid j.val)+
      (generalMeanRows 1275).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1275).c)).2-
      (generalMeanRows 1275).J/2-(generalMeanRows 1275).error 4 := by
  have he : (generalMeanRows 1275).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1275) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1275)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1275

/-! Kernel-checked entropy margins for general spectral rectangle 1276. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1276
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5551400089, 5406511515, 5266245824, 5130390329, 4998747611, 4871133955, 4747377990, 4627319503, 4510808389, 4397703740, 4287873026, 4181191381, 4077540959, 3976810367, 3878894154, 3783692355, 3691110079, 3601057138, 3513447713, 3428200053, 3345236194, 3264481713, 3185865500, 3109319545, 3034778748, 2962180745, 2891465747, 2822576387, 2755457587, 2690056429, 2626322038, 2564205474, 2503659628, 2444639133, 2387100271, 2331000896, 2276300353, 2222959410, 2170940193, 2120206118, 2070721836, 2022453177, 1975367099, 1929431639, 1884615864, 1840889834, 1798224554, 1756591939, 1715964779, 1676316700, 1637622134, 1599856289, 1562995115, 1527015281, 1491894145, 1457609730, 1424140699, 1391466332, 1359566507, 1328421674, 1298012838, 1268321541, 1239329842, 1211020298, 1183375951, 1156380310, 1130017336, 1104271425, 1079127400, 1054570491, 1030586325, 1007160914, 984280642, 961932253, 940102843, 918779844, 897951019, 877604449, 857728527, 838311942, 819343678, 800813001, 782709452, 765022838, 747743227, 730860938, 714366533, 698250815, 682504816, 667119793, 652087223, 637398794, 623046401, 609022140, 595318303, 581927371, 568842012, 556055073, 543559576, 531348714, 519415847, 507754496, 496358339, 485221208, 474337085, 463700097, 453304511, 443144734, 433215308, 423510905, 414026323, 404756489, 395696446, 386841358, 378186505, 369727277, 361459175, 353377806, 345478881, 337758214, 330211715]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1276).prefactor = (4503726369576127/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1276).cutoff/(generalMeanRows 1276).c)).2 =
    (248693178999233/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1276).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1276).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1276).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1276

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1276).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1276).criticalRate j.val*(generalMeanRows 1276).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1276).c*(generalMeanRows 1276).criticalPoint j.val)).2-
      (generalMeanRows 1276).J/2-(generalMeanRows 1276).error (generalMeanGrid j.val)+
      (generalMeanRows 1276).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1276).c)).2-
      (generalMeanRows 1276).J/2-(generalMeanRows 1276).error 4 := by
  have he : (generalMeanRows 1276).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1276) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1276)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1276

/-! Kernel-checked entropy margins for general spectral rectangle 1277. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1277
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5933575729, 5783554212, 5638229486, 5497385505, 5360821866, 5228352198, 5099802766, 4975011239, 4853825623, 4736103309, 4621710242, 4510520180, 4402414035, 4297279290, 4195009476, 4095503699, 3998666221, 3904406080, 3812636750, 3723275822, 3636244732, 3551468496, 3468875483, 3388397196, 3309968081, 3233525345, 3159008791, 3086360668, 3015525530, 2946450108, 2879083188, 2813375503, 2749279630, 2686749893, 2625742273, 2566214330, 2508125121, 2451435130, 2396106198, 2342101466, 2289385307, 2237923278, 2187682062, 2138629422, 2090734155, 2043966046, 1998295829, 1953695145, 1910136510, 1867593275, 1826039597, 1785450407, 1745801377, 1707068896, 1669230044, 1632262561, 1596144828, 1560855841, 1526375193, 1492683048, 1459760124, 1427587675, 1396147468, 1365421773, 1335393339, 1306045383, 1277361574, 1249326015, 1221923234, 1195138167, 1168956147, 1143362889, 1118344483, 1093887378, 1069978373, 1046604605, 1023753542, 1001412971, 979570986, 958215986, 937336659, 916921978, 896961189, 877443809, 858359614, 839698631, 821451134, 803607636, 786158882, 769095843, 752409708, 736091884, 720133980, 704527813, 689265393, 674338923, 659740794, 645463577, 631500019, 617843043, 604485737, 591421352, 578643301, 566145149, 553920614, 541963563, 530268002, 518828082, 507638087, 496692436, 485985676, 475512482, 465267652, 455246103, 445442872, 435853107, 426472071, 417295132, 408317768, 399535559, 390944186]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1277).prefactor = (4640871055564699/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1277).cutoff/(generalMeanRows 1277).c)).2 =
    (251098017592593/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1277).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1277).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1277).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1277

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1277).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1277).criticalRate j.val*(generalMeanRows 1277).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1277).c*(generalMeanRows 1277).criticalPoint j.val)).2-
      (generalMeanRows 1277).J/2-(generalMeanRows 1277).error (generalMeanGrid j.val)+
      (generalMeanRows 1277).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1277).c)).2-
      (generalMeanRows 1277).J/2-(generalMeanRows 1277).error 4 := by
  have he : (generalMeanRows 1277).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1277) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1277)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1277

/-! Kernel-checked entropy margins for general spectral rectangle 1278. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1278
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6420251657, 6264913639, 6114318362, 5968247366, 5826498197, 5688882755, 5555225849, 5425363932, 5299143998, 5176422607, 5057065027, 4940944471, 4827941426, 4717943045, 4610842618, 4506539083, 4404936598, 4305944152, 4209475210, 4115447400, 4023782222, 3934404786, 3847243573, 3762230218, 3679299313, 3598388217, 3519436896, 3442387766, 3367185548, 3293777142, 3222111502, 3152139524, 3083813945, 3017089241, 2951921543, 2888268549, 2826089448, 2765344847, 2705996702, 2648008256, 2591343976, 2535969504, 2481851595, 2428958075, 2377257793, 2326720574, 2277317182, 2229019278, 2181799387, 2135630858, 2090487836, 2046345228, 2003178675, 1960964523, 1919679797, 1879302177, 1839809972, 1801182098, 1763398057, 1726437914, 1690282283, 1654912299, 1620309610, 1586456352, 1553335138, 1520929039, 1489221571, 1458196679, 1427838725, 1398132473, 1369063078, 1340616073, 1312777358, 1285533188, 1258870163, 1232775217, 1207235608, 1182238911, 1157773003, 1133826061, 1110386550, 1087443214, 1064985069, 1043001397, 1021481735, 1000415871, 979793838, 959605902, 939842562, 920494538, 901552771, 883008412, 864852818, 847077548, 829674358, 812635191, 795952179, 779617633, 763624041, 747964062, 732630524, 717616416, 702914888, 688519243, 674422938, 660619573, 647102897, 633866796, 620905293, 608212546, 595782842, 583610594, 571690342, 560016744, 548584579, 537388738, 526424228, 515686163, 505169766, 494870364, 484783387]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1278).prefactor = (4782191986589367/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1278).cutoff/(generalMeanRows 1278).c)).2 =
    (1271750608834747/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1278).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1278).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1278).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1278

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1278).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1278).criticalRate j.val*(generalMeanRows 1278).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1278).c*(generalMeanRows 1278).criticalPoint j.val)).2-
      (generalMeanRows 1278).J/2-(generalMeanRows 1278).error (generalMeanGrid j.val)+
      (generalMeanRows 1278).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1278).c)).2-
      (generalMeanRows 1278).J/2-(generalMeanRows 1278).error 4 := by
  have he : (generalMeanRows 1278).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1278) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1278)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1278

/-! Kernel-checked entropy margins for general spectral rectangle 1279. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1279
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7699554073, 7511190320, 7328685287, 7151758980, 6980152904, 6813627774, 6651961510, 6494947493, 6342393038, 6194118049, 6049953842, 5909742100, 5773333951, 5640589150, 5511375349, 5385567452, 5263047029, 5143701799, 5027425163, 4914115780, 4803677190, 4696017467, 4591048910, 4488687761, 4388853940, 4291470819, 4196465000, 4103766119, 4013306667, 3925021823, 3838849299, 3754729200, 3672603892, 3592417882, 3514117707, 3437651824, 3362970520, 3290025819, 3218771393, 3149162491, 3081155862, 3014709683, 2949783498, 2886338158, 2824335760, 2763739597, 2704514106, 2646624819, 2590038320, 2534722204, 2480645031, 2427776295, 2376086382, 2325546541, 2276128848, 2227806177, 2180552168, 2134341204, 2089148380, 2044949482, 2001720958, 1959439900, 1918084017, 1877631620, 1838061597, 1799353397, 1761487009, 1724442948, 1688202235, 1652746383, 1618057381, 1584117679, 1550910172, 1518418191, 1486625485, 1455516213, 1425074927, 1395286563, 1366136431, 1337610202, 1309693899, 1282373884, 1255636854, 1229469824, 1203860127, 1178795397, 1154263566, 1130252853, 1106751758, 1083749053, 1061233774, 1039195219, 1017622933, 996506708, 975836574, 955602792, 935795851, 916406457, 897425534, 878844213, 860653827, 842845911, 825412191, 808344582, 791635183, 775276273, 759260305, 743579903, 728227856, 713197116, 698480794, 684072155, 669964615, 656151735, 642627221, 629384920, 616418813, 603723018, 591291780, 579119472, 567200593]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1279).prefactor = (5906892812905819/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1279).cutoff/(generalMeanRows 1279).c)).2 =
    (1136214737449721/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1279).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1279).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1279).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1279

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1279).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1279).criticalRate j.val*(generalMeanRows 1279).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1279).c*(generalMeanRows 1279).criticalPoint j.val)).2-
      (generalMeanRows 1279).J/2-(generalMeanRows 1279).error (generalMeanGrid j.val)+
      (generalMeanRows 1279).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1279).c)).2-
      (generalMeanRows 1279).J/2-(generalMeanRows 1279).error 4 := by
  have he : (generalMeanRows 1279).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1279) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1279)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1279

/-! Kernel-checked entropy margins for general spectral rectangle 1280. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1280
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5000595230, 4848350188, 4701479075, 4559730689, 4422871169, 4290682284, 4162959930, 4039512822, 3920161335, 3804736485, 3693079029, 3585038660, 3480473291, 3379248420, 3281236550, 3186316683, 3094373845, 3005298673, 2918987030, 2835339661, 2754261874, 2675663257, 2599457409, 2525561701, 2453897054, 2384387733, 2316961157, 2251547728, 2188080665, 2126495857, 2066731723, 2008729083, 1952431033, 1897782838, 1844731824, 1793227280, 1743220362, 1694664012, 1647512873, 1601723214, 1557252856, 1514061106, 1472108693, 1431357704, 1391771532, 1353314818, 1315953401, 1279654271, 1244385519, 1210116296, 1176816774, 1144458099, 1113012361, 1082452554, 1052752544, 1023887035, 995831537, 968562340, 942056482, 916291725, 891246527, 866900018, 843231975, 820222803, 797853509, 776105684, 754961483, 734403602, 714415265, 694980205, 676082642, 657707274, 639839256, 622464189, 605568101, 589137437, 573159043, 557620155, 542508385, 527811710, 513518458, 499617303, 486097247, 472947612, 460158033, 447718445, 435619076, 423850433, 412403302, 401268731, 390438026, 379902745, 369654685, 359685879, 349988589, 340555295, 331378694, 322451689, 313767385, 305319083, 297100273, 289104630, 281326007, 273758431, 266396097, 259233363, 252264747, 245484919, 238888700, 232471056, 226227093, 220152055, 214241318, 208490387, 202894893, 197450589, 192153344, 186999145, 181984087, 177104377, 172356325]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1280).prefactor = (4927816335077389/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1280).cutoff/(generalMeanRows 1280).c)).2 =
    (1181670175727699/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1280).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1280).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1280).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1280

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1280).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1280).criticalRate j.val*(generalMeanRows 1280).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1280).c*(generalMeanRows 1280).criticalPoint j.val)).2-
      (generalMeanRows 1280).J/2-(generalMeanRows 1280).error (generalMeanGrid j.val)+
      (generalMeanRows 1280).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1280).c)).2-
      (generalMeanRows 1280).J/2-(generalMeanRows 1280).error 4 := by
  have he : (generalMeanRows 1280).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1280) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1280)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1280

/-! Kernel-checked entropy margins for general spectral rectangle 1281. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1281
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5818191644, 5656851008, 5500857687, 5349964868, 5203943169, 5062578881, 4925672426, 4793037019, 4664497485, 4539889220, 4419057269, 4301855514, 4188145945, 4077798014, 3970688055, 3866698762, 3765718726, 3667642005, 3572367747, 3479799842, 3389846606, 3302420493, 3217437836, 3134818603, 3054486179, 2976367163, 2900391182, 2826490719, 2754600954, 2684659619, 2616606858, 2550385104, 2485938961, 2423215094, 2362162124, 2302730539, 2244872599, 2188542257, 2133695075, 2080288158, 2028280080, 1977630820, 1928301701, 1880255333, 1833455560, 1787867406, 1743457026, 1700191664, 1658039608, 1616970145, 1576953528, 1537960934, 1499964432, 1462936948, 1426852232, 1391684832, 1357410058, 1324003962, 1291443305, 1259705538, 1228768773, 1198611762, 1169213875, 1140555080, 1112615921, 1085377501, 1058821459, 1032929958, 1007685664, 983071733, 959071791, 935669922, 912850653, 890598941, 868900155, 847740070, 827104850, 806981036, 787355537, 768215618, 749548887, 731343288, 713587088, 696268870, 679377523, 662902231, 646832467, 631157984, 615868806, 600955220, 586407770, 572217249, 558374690, 544871364, 531698767, 518848618, 506312853, 494083616, 482153254, 470514315, 459159537, 448081847, 437274352, 426730339, 416443266, 406406759, 396614606, 387060755, 377739309, 368644520, 359770786, 351112649, 342664788, 334422019, 326379285, 318531663, 310874348, 303402661, 296112039, 288998033, 282056308]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1281).prefactor = (5077875146032001/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1281).cutoff/(generalMeanRows 1281).c)).2 =
    (121984274923273/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1281).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1281).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1281).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1281

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1281).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1281).criticalRate j.val*(generalMeanRows 1281).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1281).c*(generalMeanRows 1281).criticalPoint j.val)).2-
      (generalMeanRows 1281).J/2-(generalMeanRows 1281).error (generalMeanGrid j.val)+
      (generalMeanRows 1281).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1281).c)).2-
      (generalMeanRows 1281).J/2-(generalMeanRows 1281).error 4 := by
  have he : (generalMeanRows 1281).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1281) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1281)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1281

/-! Kernel-checked entropy margins for general spectral rectangle 1282. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1282
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7111174957, 6941055807, 6776098468, 6616065017, 6460735024, 6309903733, 6163380487, 6020987340, 5882557854, 5747936028, 5616975364, 5489538031, 5365494126, 5244721021, 5127102771, 5012529589, 4900897377, 4792107294, 4686065380, 4582682201, 4481872541, 4383555111, 4287652291, 4194089891, 4102796932, 4013705451, 3926750314, 3841869047, 3759001685, 3678090628, 3599080504, 3521918054, 3446552011, 3372933003, 3301013446, 3230747461, 3162090783, 3095000687, 3029435908, 2965356579, 2902724157, 2841501372, 2781652163, 2723141626, 2665935964, 2610002441, 2555309334, 2501825895, 2449522305, 2398369643, 2348339846, 2299405676, 2251540691, 2204719210, 2158916287, 2114107684, 2070269843, 2027379864, 1985415479, 1944355032, 1904177454, 1864862249, 1826389466, 1788739690, 1751894014, 1715834032, 1680541816, 1645999903, 1612191281, 1579099372, 1546708022, 1515001484, 1483964408, 1453581829, 1423839153, 1394722151, 1366216940, 1338309982, 1310988067, 1284238306, 1258048124, 1232405246, 1207297693, 1182713773, 1158642071, 1135071442, 1111991006, 1089390136, 1067258457, 1045585835, 1024362371, 1003578397, 983224467, 963291354, 943770042, 924651723, 905927787, 887589824, 869629612, 852039115, 834810481, 817936033, 801408266, 785219844, 769363595, 753832508, 738619724, 723718541, 709122404, 694824900, 680819761, 667100856, 653662188, 640497892, 627602230, 614969592, 602594487, 590471546, 578595517, 566961259, 555563745]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1282).prefactor = (1308125863739429/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1282).cutoff/(generalMeanRows 1282).c)).2 =
    (1275857390787401/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1282).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1282).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1282).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1282

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1282).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1282).criticalRate j.val*(generalMeanRows 1282).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1282).c*(generalMeanRows 1282).criticalPoint j.val)).2-
      (generalMeanRows 1282).J/2-(generalMeanRows 1282).error (generalMeanGrid j.val)+
      (generalMeanRows 1282).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1282).c)).2-
      (generalMeanRows 1282).J/2-(generalMeanRows 1282).error 4 := by
  have he : (generalMeanRows 1282).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1282) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1282)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1282

/-! Kernel-checked entropy margins for general spectral rectangle 1283. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1283
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5159075539, 5019881754, 4885199022, 4754823479, 4628565220, 4506246941, 4387702754, 4272777142, 4161324035, 4053205998, 3948293500, 3846464274, 3747602732, 3651599451, 3558350705, 3467758045, 3379727919, 3294171331, 3211003523, 3130143695, 3051514743, 2975043024, 2900658138, 2828292730, 2757882304, 2689365060, 2622681731, 2557775449, 2494591604, 2433077725, 2373183366, 2314859998, 2258060914, 2202741132, 2148857315, 2096367685, 2045231952, 1995411246, 1946868044, 1899566116, 1853470461, 1808547257, 1764763808, 1722088495, 1680490730, 1639940918, 1600410407, 1561871458, 1524297206, 1487661622, 1451939487, 1417106353, 1383138522, 1350013010, 1317707525, 1286200441, 1255470774, 1225498158, 1196262821, 1167745569, 1139927763, 1112791299, 1086318591, 1060492555, 1035296588, 1010714556, 986730777, 963330005, 940497418, 918218604, 896479547, 875266615, 854566547, 834366443, 814653752, 795416261, 776642086, 758319659, 740437724, 722985321, 705951781, 689326718, 673100018, 657261834, 641802575, 626712901, 611983715, 597606157, 583571596, 569871621, 556498043, 543442878, 530698351, 518256882, 506111088, 494253772, 482677919, 471376694, 460343433, 449571643, 439054991, 428787306, 418762571, 408974920, 399418634, 390088137, 380977991, 372082894, 363397677, 354917298, 346636840, 338551508, 330656626, 322947633, 315420079, 308069627, 300892043, 293883200, 287039069, 280355722, 273829328]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1283).prefactor = (4265702382831907/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1283).cutoff/(generalMeanRows 1283).c)).2 =
    (1376765437774039/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1283).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1283).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1283).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1283

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1283).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1283).criticalRate j.val*(generalMeanRows 1283).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1283).c*(generalMeanRows 1283).criticalPoint j.val)).2-
      (generalMeanRows 1283).J/2-(generalMeanRows 1283).error (generalMeanGrid j.val)+
      (generalMeanRows 1283).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1283).c)).2-
      (generalMeanRows 1283).J/2-(generalMeanRows 1283).error 4 := by
  have he : (generalMeanRows 1283).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1283) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1283)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1283

/-! Kernel-checked entropy margins for general spectral rectangle 1284. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1284
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5283936869, 5142778042, 5006165486, 4873893877, 4745771986, 4621621306, 4501274854, 4384576108, 4271378081, 4161542493, 4054939038, 3951444727, 3850943309, 3753324743, 3658484729, 3566324282, 3476749350, 3389670465, 3305002428, 3222664021, 3142577748, 3064669592, 2988868799, 2915107677, 2843321409, 2773447885, 2705427546, 2639203238, 2574720079, 2511925335, 2450768305, 2391200214, 2333174115, 2276644794, 2221568686, 2167903793, 2115609611, 2064647056, 2014978400, 1966567209, 1919378284, 1873377607, 1828532291, 1784810525, 1742181538, 1700615546, 1660083721, 1620558141, 1582011765, 1544418389, 1507752620, 1471989841, 1437106181, 1403078490, 1369884311, 1337501852, 1305909966, 1275088124, 1245016396, 1215675429, 1187046424, 1159111124, 1131851786, 1105251173, 1079292530, 1053959571, 1029236465, 1005107818, 981558661, 958574435, 936140979, 914244517, 892871647, 872009327, 851644866, 831765913, 812360446, 793416761, 774923465, 756869465, 739243961, 722036434, 705236640, 688834602, 672820603, 657185175, 641919097, 627013383, 612459279, 598248255, 584371999, 570822409, 557591590, 544671848, 532055683, 519735782, 507705019, 495956447, 484483291, 473278947, 462336975, 451651097, 441215191, 431023284, 421069555, 411348325, 401854056, 392581346, 383524926, 374679658, 366040527, 357602644, 349361238, 341311656, 333449357, 325769911, 318268997, 310942398, 303785999, 296795785, 289967840]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1284).prefactor = (2158602704030613/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1284).cutoff/(generalMeanRows 1284).c)).2 =
    (345154751772507/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1284).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1284).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1284).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1284

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1284).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1284).criticalRate j.val*(generalMeanRows 1284).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1284).c*(generalMeanRows 1284).criticalPoint j.val)).2-
      (generalMeanRows 1284).J/2-(generalMeanRows 1284).error (generalMeanGrid j.val)+
      (generalMeanRows 1284).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1284).c)).2-
      (generalMeanRows 1284).J/2-(generalMeanRows 1284).error 4 := by
  have he : (generalMeanRows 1284).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1284) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1284)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1284

/-! Kernel-checked entropy margins for general spectral rectangle 1285. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1285
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5444876359, 5299418081, 5158644545, 5022344174, 4890319913, 4762387821, 4638375826, 4518122640, 4401476799, 4288295811, 4178445400, 4071798833, 3968236317, 3867644460, 3769915785, 3674948292, 3582645064, 3492913908, 3405667030, 3320820739, 3238295178, 3158014076, 3079904524, 3003896766, 2929924014, 2857922264, 2787830144, 2719588760, 2653141556, 2588434194, 2525414428, 2464031997, 2404238524, 2345987419, 2289233789, 2233934357, 2180047386, 2127532600, 2076351123, 2026465412, 1977839195, 1930437418, 1884226191, 1839172737, 1795245345, 1752413326, 1710646972, 1669917512, 1630197080, 1591458676, 1553676132, 1516824081, 1480877926, 1445813811, 1411608595, 1378239823, 1345685703, 1313925082, 1282937422, 1252702780, 1223201786, 1194415624, 1166326015, 1138915193, 1112165895, 1086061339, 1060585211, 1035721647, 1011455224, 987770938, 964654199, 942090809, 920066958, 898569209, 877584482, 857100051, 837103526, 817582850, 798526280, 779922388, 761760041, 744028403, 726716916, 709815301, 693313543, 677201888, 661470831, 646111116, 631113719, 616469853, 602170950, 588208663, 574574856, 561261602, 548261170, 535566026, 523168828, 511062414, 499239806, 487694197, 476418952, 465407601, 454653835, 444151501, 433894599, 423877277, 414093829, 404538688, 395206426, 386091746, 377189482, 368494596, 360002172, 351707413, 343605642, 335692294, 327962915, 320413160, 313038790, 305835667, 298799754]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1285).prefactor = (2224349973012909/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1285).cutoff/(generalMeanRows 1285).c)).2 =
    (345154751772507/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1285).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1285).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1285).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1285

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1285).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1285).criticalRate j.val*(generalMeanRows 1285).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1285).c*(generalMeanRows 1285).criticalPoint j.val)).2-
      (generalMeanRows 1285).J/2-(generalMeanRows 1285).error (generalMeanGrid j.val)+
      (generalMeanRows 1285).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1285).c)).2-
      (generalMeanRows 1285).J/2-(generalMeanRows 1285).error 4 := by
  have he : (generalMeanRows 1285).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1285) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1285)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1285

/-! Kernel-checked entropy margins for general spectral rectangle 1286. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1286
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5814994509, 5664284533, 5518338450, 5376941393, 5239893366, 5107007783, 4978110198, 4853037181, 4731635332, 4613760407, 4499276539, 4388055546, 4279976315, 4174924246, 4072790753, 3973472818, 3876872584, 3782896989, 3691457431, 3602469468, 3515852541, 3431529722, 3349427482, 3269475483, 3191606380, 3115755646, 3041861406, 2969864284, 2899707265, 2831335563, 2764696503, 2699739406, 2636415488, 2574677762, 2514480948, 2455781387, 2398536968, 2342707046, 2288252382, 2235135070, 2183318485, 2132767217, 2083447025, 2035324783, 1988368432, 1942546936, 1897830242, 1854189236, 1811595706, 1770022309, 1729442534, 1689830671, 1651161782, 1613411667, 1576556842, 1540574510, 1505442537, 1471139427, 1437644299, 1404936869, 1372997423, 1341806806, 1311346393, 1281598079, 1252544257, 1224167806, 1196452070, 1169380846, 1142938369, 1117109298, 1091878702, 1067232048, 1043155187, 1019634346, 996656111, 974207420, 952275552, 930848117, 909913042, 889458567, 869473236, 849945882, 830865625, 812221861, 794004253, 776202728, 758807462, 741808882, 725197651, 708964667, 693101053, 677598152, 662447523, 647640931, 633170344, 619027930, 605206045, 591697235, 578494224, 565589917, 552977389, 540649884, 528600806, 516823724, 505312356, 494060575, 483062399, 472311990, 461803649, 451531814, 441491055, 431676071, 422081686, 412702849, 403534627, 394572204, 385810877, 377246055, 368873255, 360688099, 352686311]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1286).prefactor = (4584199577999189/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1286).cutoff/(generalMeanRows 1286).c)).2 =
    (1392269624310021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1286).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1286).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1286).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1286

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1286).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1286).criticalRate j.val*(generalMeanRows 1286).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1286).c*(generalMeanRows 1286).criticalPoint j.val)).2-
      (generalMeanRows 1286).J/2-(generalMeanRows 1286).error (generalMeanGrid j.val)+
      (generalMeanRows 1286).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1286).c)).2-
      (generalMeanRows 1286).J/2-(generalMeanRows 1286).error 4 := by
  have he : (generalMeanRows 1286).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1286) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1286)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1286

/-! Kernel-checked entropy margins for general spectral rectangle 1287. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1287
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6360618579, 6204223751, 6052621400, 5905595390, 5762944754, 5624482197, 5490032782, 5359432777, 5232528642, 5109176128, 4989239477, 4872590717, 4759109024, 4648680154, 4541195935, 4436553805, 4334656403, 4235411187, 4138730098, 4044529251, 3952728656, 3863251953, 3776026190, 3690981595, 3608051389, 3527171600, 3448280897, 3371320437, 3296233722, 3222966468, 3151466485, 3081683561, 3013569360, 2947077323, 2882162580, 2818781862, 2756893422, 2696456966, 2637433579, 2579785663, 2523476875, 2468472071, 2414737254, 2362239521, 2310947016, 2260828888, 2211855248, 2163997126, 2117226440, 2071515952, 2026839245, 1983170680, 1940485375, 1898759172, 1857968608, 1818090897, 1779103895, 1740986084, 1703716549, 1667274954, 1631641523, 1596797022, 1562722738, 1529400466, 1496812486, 1464941552, 1433770874, 1403284104, 1373465322, 1344299021, 1315770098, 1287863836, 1260565896, 1233862306, 1207739445, 1182184037, 1157183141, 1132724138, 1108794722, 1085382894, 1062476950, 1040065475, 1018137332, 996681655, 975687845, 955145556, 935044694, 915375407, 896128078, 877293322, 858861974, 840825090, 823173936, 805899982, 788994903, 772450565, 756259026, 740412531, 724903502, 709724538, 694868412, 680328060, 666096582, 652167239, 638533443, 625188759, 612126898, 599341714, 586827202, 574577492, 562586849, 550849664, 539360459, 528113876, 517104678, 506327747, 495778079, 485450782, 475341072, 465444275, 455755816]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1287).prefactor = (73809785814861/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1287).cutoff/(generalMeanRows 1287).c)).2 =
    (1411994129657799/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1287).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1287).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1287).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1287

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1287).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1287).criticalRate j.val*(generalMeanRows 1287).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1287).c*(generalMeanRows 1287).criticalPoint j.val)).2-
      (generalMeanRows 1287).J/2-(generalMeanRows 1287).error (generalMeanGrid j.val)+
      (generalMeanRows 1287).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1287).c)).2-
      (generalMeanRows 1287).J/2-(generalMeanRows 1287).error 4 := by
  have he : (generalMeanRows 1287).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1287) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1287)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1287

/-! Kernel-checked entropy margins for general spectral rectangle 1288. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1288
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6902499973, 6743801958, 6589791854, 6440257438, 6295001654, 6153841100, 6016604705, 5883132562, 5753274907, 5626891208, 5503849366, 5384024998, 5267300797, 5153565965, 5042715696, 4934650722, 4829276889, 4726504789, 4626249412, 4528429846, 4432968989, 4339793293, 4248832534, 4160019596, 4073290274, 3988583093, 3905839145, 3825001935, 3746017239, 3668832976, 3593399087, 3519667424, 3447591644, 3377127118, 3308230837, 3240861330, 3174978589, 3110543994, 3047520247, 2985871308, 2925562336, 2866559632, 2808830592, 2752343651, 2697068243, 2642974755, 2590034487, 2538219613, 2487503144, 2437858898, 2389261462, 2341686165, 2295109048, 2249506836, 2204856915, 2161137302, 2118326625, 2076404102, 2035349517, 1995143200, 1955766009, 1917199313, 1879424970, 1842425315, 1806183143, 1770681691, 1735904626, 1701836031, 1668460393, 1635762586, 1603727861, 1572341838, 1541590488, 1511460128, 1481937406, 1453009295, 1424663081, 1396886356, 1369667006, 1342993205, 1316853406, 1291236333, 1266130973, 1241526570, 1217412618, 1193778851, 1170615240, 1147911986, 1125659511, 1103848458, 1082469677, 1061514228, 1040973369, 1020838553, 1001101427, 981753819, 962787741, 944195380, 925969094, 908101411, 890585019, 873412769, 856577663, 840072859, 823891661, 808027515, 792474013, 777224880, 762273977, 747615296, 733242957, 719151204, 705334405, 691787044, 678503724, 665479160, 652708181, 640185720, 627906820, 615866625, 604060382]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1288).prefactor = (1192826819238911/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1288).cutoff/(generalMeanRows 1288).c)).2 =
    (287237771648971/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1288).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1288).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1288).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1288

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1288).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1288).criticalRate j.val*(generalMeanRows 1288).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1288).c*(generalMeanRows 1288).criticalPoint j.val)).2-
      (generalMeanRows 1288).J/2-(generalMeanRows 1288).error (generalMeanGrid j.val)+
      (generalMeanRows 1288).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1288).c)).2-
      (generalMeanRows 1288).J/2-(generalMeanRows 1288).error 4 := by
  have he : (generalMeanRows 1288).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1288) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1288)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1288

/-! Kernel-checked entropy margins for general spectral rectangle 1289. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1289
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4724387371, 4588262060, 4456735459, 4329599780, 4206660961, 4087737397, 3972658820, 3861265307, 3753406398, 3648940311, 3547733243, 3449658736, 3354597120, 3262434997, 3173064788, 3086384310, 3002296408, 2920708604, 2841532791, 2764684942, 2690084856, 2617655913, 2547324860, 2479021604, 2412679031, 2348232833, 2285621348, 2224785417, 2165668245, 2108215276, 2052374077, 1998094227, 1945327217, 1894026354, 1844146672, 1795644850, 1748479136, 1702609269, 1657996417, 1614603107, 1572393168, 1531331674, 1491384888, 1452520213, 1414706144, 1377912222, 1342108993, 1307267965, 1273361570, 1240363132, 1208246823, 1176987640, 1146561369, 1116944552, 1088114468, 1060049095, 1032727093, 1006127774, 980231082, 955017568, 930468370, 906565192, 883290286, 860626429, 838556909, 817065509, 796136485, 775754555, 755904880, 736573053, 717745084, 699407383, 681546754, 664150375, 647205791, 630700900, 614623944, 598963496, 583708452, 568848017, 554371702, 540269308, 526530922, 513146905, 500107885, 487404751, 475028641, 462970939, 451223265, 439777466, 428625617, 417760004, 407173128, 396857689, 386806589, 377012921, 367469963, 358171178, 349110202, 340280843, 331677076, 323293038, 315123021, 307161472, 299402984, 291842296, 284474287, 277293969, 270296492, 263477130, 256831285, 250354478, 244042350, 237890659, 231895270, 226052162, 220357416, 214807219, 209397855, 204125708, 198987256]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1289).prefactor = (1037022564754973/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1289).cutoff/(generalMeanRows 1289).c)).2 =
    (1551118824918831/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1289).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1289).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1289).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1289

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1289).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1289).criticalRate j.val*(generalMeanRows 1289).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1289).c*(generalMeanRows 1289).criticalPoint j.val)).2-
      (generalMeanRows 1289).J/2-(generalMeanRows 1289).error (generalMeanGrid j.val)+
      (generalMeanRows 1289).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1289).c)).2-
      (generalMeanRows 1289).J/2-(generalMeanRows 1289).error 4 := by
  have he : (generalMeanRows 1289).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1289) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1289)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1289

/-! Kernel-checked entropy margins for general spectral rectangle 1290. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1290
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5648448298, 5487052134, 5331085880, 5180302721, 5034472499, 4893380119, 4756824143, 4624615562, 4496576701, 4372540258, 4252348442, 4135852209, 4022910575, 3913389999, 3807163834, 3704111819, 3604119635, 3507078490, 3412884745, 3321439581, 3232648679, 3146421945, 3062673244, 2981320163, 2902283794, 2825488524, 2750861857, 2678334234, 2607838875, 2539311630, 2472690844, 2407917223, 2344933717, 2283685409, 2224119411, 2166184763, 2109832346, 2055014793, 2001686411, 1949803103, 1899322299, 1850202888, 1802405157, 1755890728, 1710622503, 1666564615, 1623682369, 1581942205, 1541311644, 1501759250, 1463254589, 1425768189, 1389271502, 1353736875, 1319137510, 1285447436, 1252641479, 1220695229, 1189585021, 1159287898, 1129781595, 1101044511, 1073055686, 1045794778, 1019242046, 993378327, 968185014, 943644045, 919737876, 896449471, 873762283, 851660238, 830127720, 809149556, 788711003, 768797733, 749395823, 730491739, 712072325, 694124792, 676636706, 659595979, 642990856, 626809906, 611042013, 595676366, 580702449, 566110035, 551889173, 538030185, 524523654, 511360418, 498531564, 486028418, 473842539, 461965714, 450389950, 439107468, 428110695, 417392264, 406945000, 396761921, 386836230, 377161311, 367730721, 358538190, 349577611, 340843040, 332328688, 324028920, 315938246, 308051323, 300362947, 292868050, 285561696, 278439078, 271495514, 264726447, 258127433, 251694149, 245422382]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1290).prefactor = (501596761057181/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1290).cutoff/(generalMeanRows 1290).c)).2 =
    (676975380003933/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1290).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1290).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1290).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1290

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1290).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1290).criticalRate j.val*(generalMeanRows 1290).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1290).c*(generalMeanRows 1290).criticalPoint j.val)).2-
      (generalMeanRows 1290).J/2-(generalMeanRows 1290).error (generalMeanGrid j.val)+
      (generalMeanRows 1290).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1290).c)).2-
      (generalMeanRows 1290).J/2-(generalMeanRows 1290).error 4 := by
  have he : (generalMeanRows 1290).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1290) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1290)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1290

/-! Kernel-checked entropy margins for general spectral rectangle 1291. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1291
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6959700648, 6788575596, 6622694406, 6461820585, 6305734237, 6154230427, 6007117741, 5864217027, 5725360282, 5590389671, 5459156651, 5331521196, 5207351101, 5086521362, 4968913620, 4854415654, 4742920929, 4634328189, 4528541082, 4425467823, 4325020884, 4227116717, 4131675496, 4038620879, 3947879798, 3859382254, 3773061141, 3688852073, 3606693230, 3526525217, 3448290927, 3371935419, 3297405805, 3224651141, 3153622329, 3084272026, 3016554553, 2950425821, 2885843250, 2822765699, 2761153404, 2700967911, 2642172019, 2584729727, 2528606180, 2473767619, 2420181341, 2367815648, 2316639811, 2266624030, 2217739396, 2169957858, 2123252189, 2077595956, 2032963487, 1989329848, 1946670811, 1904962832, 1864183023, 1824309135, 1785319529, 1747193159, 1709909551, 1673448782, 1637791467, 1602918733, 1568812209, 1535454008, 1502826709, 1470913348, 1439697395, 1409162751, 1379293724, 1350075025, 1321491753, 1293529381, 1266173747, 1239411044, 1213227809, 1187610912, 1162547546, 1138025220, 1114031750, 1090555246, 1067584110, 1045107022, 1023112938, 1001591077, 980530917, 959922187, 939754863, 920019154, 900705506, 881804586, 863307282, 845204697, 827488140, 810149124, 793179359, 776570748, 760315380, 744405529, 728833644, 713592349, 698674439, 684072871, 669780763, 655791392, 642098187, 628694725, 615574729, 602732064, 590160735, 577854879, 565808768, 554016800, 542473499, 531173514, 520111610, 509282671, 498681694]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1291).prefactor = (5168745225036461/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1291).cutoff/(generalMeanRows 1291).c)).2 =
    (1411994129657799/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1291).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1291).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1291).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1291

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1291).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1291).criticalRate j.val*(generalMeanRows 1291).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1291).c*(generalMeanRows 1291).criticalPoint j.val)).2-
      (generalMeanRows 1291).J/2-(generalMeanRows 1291).error (generalMeanGrid j.val)+
      (generalMeanRows 1291).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1291).c)).2-
      (generalMeanRows 1291).J/2-(generalMeanRows 1291).error 4 := by
  have he : (generalMeanRows 1291).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1291) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1291)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1291

/-! Kernel-checked entropy margins for general spectral rectangle 1292. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1292
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8254950389, 8080547651, 7911088762, 7746347560, 7586114417, 7430194563, 7278406632, 7130581379, 6986560553, 6846195902, 6709348288, 6575886905, 6445688577, 6318637133, 6194622845, 6073541925, 5955296070, 5839792052, 5726941346, 5616659792, 5508867290, 5403487522, 5300447694, 5199678307, 5101112941, 5004688064, 4910342845, 4818018998, 4727660621, 4639214062, 4552627788, 4467852262, 4384839835, 4303544642, 4223922505, 4145930845, 4069528600, 3994676146, 3921335226, 3849468881, 3779041390, 3710018209, 3642365915, 3576052156, 3511045602, 3447315900, 3384833630, 3323570262, 3263498124, 3204590362, 3146820907, 3090164441, 3034596373, 2980092801, 2926630493, 2874186858, 2822739923, 2772268307, 2722751201, 2674168350, 2626500026, 2579727019, 2533830609, 2488792555, 2444595079, 2401220847, 2358652955, 2316874918, 2275870654, 2235624468, 2196121047, 2157345443, 2119283060, 2081919649, 2045241292, 2009234397, 1973885684, 1939182176, 1905111195, 1871660347, 1838817519, 1806570869, 1774908817, 1743820040, 1713293465, 1683318260, 1653883828, 1624979805, 1596596046, 1568722627, 1541349834, 1514468159, 1488068298, 1462141139, 1436677763, 1411669438, 1387107612, 1362983910, 1339290131, 1316018243, 1293160375, 1270708820, 1248656027, 1226994597, 1205717279, 1184816972, 1164286713, 1144119681, 1124309189, 1104848685, 1085731743, 1066952069, 1048503488, 1030379950, 1012575522, 995084385, 977900836, 961019282, 944434238, 928140326, 912132270]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1292).prefactor = (1311717568975911/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1292).cutoff/(generalMeanRows 1292).c)).2 =
    (1465176395118109/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1292).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1292).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1292).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1292

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1292).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1292).criticalRate j.val*(generalMeanRows 1292).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1292).c*(generalMeanRows 1292).criticalPoint j.val)).2-
      (generalMeanRows 1292).J/2-(generalMeanRows 1292).error (generalMeanGrid j.val)+
      (generalMeanRows 1292).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1292).c)).2-
      (generalMeanRows 1292).J/2-(generalMeanRows 1292).error 4 := by
  have he : (generalMeanRows 1292).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1292) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1292)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1292

/-! Kernel-checked entropy margins for general spectral rectangle 1293. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1293
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5408454339, 5262444080, 5121160366, 4984391137, 4851938574, 4723617760, 4599255500, 4478689280, 4361766344, 4248342865, 4138283219, 4031459321, 3927750036, 3827040651, 3729222395, 3634192007, 3541851339, 3452107009, 3364870070, 3280055716, 3197583016, 3117374662, 3039356749, 2963458561, 2889612382, 2817753324, 2747819160, 2679750174, 2613489025, 2548980616, 2486171974, 2425012141, 2365452070, 2307444527, 2250944003, 2195906630, 2142290099, 2090053592, 2039157709, 1989564405, 1941236927, 1894139760, 1848238572, 1803500161, 1759892411, 1717384244, 1675945577, 1635547283, 1596161155, 1557759864, 1520316929, 1483806683, 1448204243, 1413485478, 1379626986, 1346606060, 1314400669, 1282989431, 1252351592, 1222466999, 1193316084, 1164879843, 1137139815, 1110078064, 1083677163, 1057920174, 1032790637, 1008272548, 984350348, 961008911, 938233523, 916009877, 894324055, 873162516, 852512088, 832359953, 812693637, 793501002, 774770233, 756489828, 738648591, 721235623, 704240310, 687652319, 671461585, 655658308, 640232943, 625176192, 610478998, 596132538, 582128218, 568457662, 555112712, 542085416, 529368028, 516952997, 504832964, 493000759, 481449391, 470172046, 459162085, 448413032, 437918576, 427672564, 417668997, 407902026, 398365948, 389055202, 379964366, 371088152, 362421404, 353959093, 345696314, 337628284, 329750338, 322057926, 314546610, 307212059, 300050053, 293056470, 286227292]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1293).prefactor = (875465641555009/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1293).cutoff/(generalMeanRows 1293).c)).2 =
    (781744329633157/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1293).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1293).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1293).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1293

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1293).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1293).criticalRate j.val*(generalMeanRows 1293).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1293).c*(generalMeanRows 1293).criticalPoint j.val)).2-
      (generalMeanRows 1293).J/2-(generalMeanRows 1293).error (generalMeanGrid j.val)+
      (generalMeanRows 1293).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1293).c)).2-
      (generalMeanRows 1293).J/2-(generalMeanRows 1293).error 4 := by
  have he : (generalMeanRows 1293).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1293) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1293)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1293

/-! Kernel-checked entropy margins for general spectral rectangle 1294. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1294
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5703887422, 5552864212, 5406670401, 5265089591, 5127919990, 4994973031, 4866072157, 4741051756, 4619756200, 4502039005, 4387762075, 4276795025, 4169014572, 4064303996, 3962552643, 3863655484, 3767512711, 3674029372, 3583115037, 3494683501, 3408652500, 3324943465, 3243481285, 3164194098, 3087013093, 3011872332, 2938708582, 2867461163, 2798071804, 2730484516, 2664645463, 2600502854, 2538006837, 2477109398, 2417764272, 2359926856, 2303554128, 2248604576, 2195038125, 2142816068, 2091901012, 2042256813, 1993848523, 1946642343, 1900605566, 1855706539, 1811914615, 1769200113, 1727534282, 1686889259, 1647238040, 1608554442, 1570813075, 1533989311, 1498059254, 1462999717, 1428788194, 1395402832, 1362822417, 1331026341, 1299994588, 1269707711, 1240146814, 1211293531, 1183130010, 1155638896, 1128803314, 1102606854, 1077033556, 1052067895, 1027694766, 1003899476, 980667724, 957985593, 935839538, 914216374, 893103265, 872487714, 852357551, 832700928, 813506302, 794762433, 776458373, 758583454, 741127287, 724079745, 707430966, 691171334, 675291483, 659782282, 644634832, 629840460, 615390710, 601277340, 587492313, 574027795, 560876148, 548029923, 535481856, 523224864, 511252040, 499556647, 488132114, 476972032, 466070151, 455420372, 445016747, 434853473, 424924889, 415225470, 405749828, 396492706, 387448973, 378613622, 369981770, 361548648, 353309605, 345260101, 337395706, 329712095, 322205048]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1294).prefactor = (4510119519826731/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1294).cutoff/(generalMeanRows 1294).c)).2 =
    (1571035864901697/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1294).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1294).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1294).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1294

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1294).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1294).criticalRate j.val*(generalMeanRows 1294).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1294).c*(generalMeanRows 1294).criticalPoint j.val)).2-
      (generalMeanRows 1294).J/2-(generalMeanRows 1294).error (generalMeanGrid j.val)+
      (generalMeanRows 1294).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1294).c)).2-
      (generalMeanRows 1294).J/2-(generalMeanRows 1294).error 4 := by
  have he : (generalMeanRows 1294).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1294) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1294)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1294

/-! Kernel-checked entropy margins for general spectral rectangle 1295. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1295
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6229821559, 6072967006, 5920977605, 5773635680, 5630738442, 5492096567, 5357532953, 5226881615, 5099986708, 4976701657, 4856888386, 4740416620, 4627163266, 4517011859, 4409852049, 4305579157, 4204093758, 4105301310, 4009111813, 3915439504, 3824202574, 3735322908, 3648725855, 3564340006, 3482096999, 3401931336, 3323780215, 3247583373, 3173282944, 3100823325, 3030151054, 2961214696, 2893964735, 2828353475, 2764334951, 2701864841, 2640900384, 2581400308, 2523324758, 2466635232, 2411294516, 2357266630, 2304516771, 2253011261, 2202717501, 2153603924, 2105639954, 2058795961, 2013043228, 1968353909, 1924701002, 1882058309, 1840400408, 1799702626, 1759941008, 1721092291, 1683133879, 1646043821, 1609800785, 1574384037, 1539773422, 1505949344, 1472892742, 1440585079, 1409008321, 1378144920, 1347977801, 1318490340, 1289666360, 1261490108, 1233946243, 1207019829, 1180696316, 1154961529, 1129801662, 1105203260, 1081153212, 1057638741, 1034647393, 1012167028, 990185811, 968692203, 947674952, 927123087, 907025907, 887372976, 868154114, 849359389, 830979114, 813003836, 795424334, 778231606, 761416872, 744971559, 728887303, 713155939, 697769496, 682720195, 668000439, 653602815, 639520081, 625745168, 612271175, 599091359, 586199140, 573588088, 561251925, 549184519, 537379880, 525832158, 514535638, 503484737, 492674003, 482098106, 471751842, 461630124, 451727984, 442040567, 432563128, 423291031, 414219747]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1295).prefactor = (290433700616051/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1295).cutoff/(generalMeanRows 1295).c)).2 =
    (795078453174237/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1295).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1295).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1295).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1295

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1295).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1295).criticalRate j.val*(generalMeanRows 1295).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1295).c*(generalMeanRows 1295).criticalPoint j.val)).2-
      (generalMeanRows 1295).J/2-(generalMeanRows 1295).error (generalMeanGrid j.val)+
      (generalMeanRows 1295).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1295).c)).2-
      (generalMeanRows 1295).J/2-(generalMeanRows 1295).error 4 := by
  have he : (generalMeanRows 1295).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1295) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1295)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1295

/-! Kernel-checked entropy margins for general spectral rectangle 1296. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1296
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6828567445, 6669068703, 6514312691, 6364086682, 6218192796, 6076446559, 5938675656, 5804718806, 5674424791, 5547651571, 5424265509, 5304140674, 5187158218, 5073205812, 4962177149, 4853971479, 4748493209, 4645651518, 4545360029, 4447536496, 4352102523, 4258983310, 4168107418, 4079406553, 3992815370, 3908271296, 3825714353, 3745087017, 3666334067, 3589402459, 3514241200, 3440801243, 3369035373, 3298898120, 3230345660, 3163335737, 3097827584, 3033781844, 2971160511, 2909926857, 2850045379, 2791481738, 2734202708, 2678176129, 2623370856, 2569756717, 2517304471, 2465985774, 2415773132, 2366639876, 2318560125, 2271508755, 2225461368, 2180394269, 2136284432, 2093109484, 2050847674, 2009477852, 1968979448, 1929332453, 1890517397, 1852515331, 1815307809, 1778876871, 1743205029, 1708275247, 1674070931, 1640575911, 1607774428, 1575651125, 1544191027, 1513379537, 1483202420, 1453645790, 1424696107, 1396340158, 1368565052, 1341358212, 1314707362, 1288600519, 1263025988, 1237972350, 1213428456, 1189383419, 1165826608, 1142747638, 1120136366, 1097982885, 1076277514, 1055010797, 1034173491, 1013756565, 993751195, 974148754, 954940811, 936119124, 917675636, 899602471, 881891926, 864536471, 847528744, 830861542, 814527824, 798520701, 782833438, 767459445, 752392275, 737625625, 723153324, 708969338, 695067761, 681442817, 668088853, 655000335, 642171852, 629598105, 617273909, 605194190, 593353983, 581748426, 570372760]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1296).prefactor = (1173365496129459/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1296).cutoff/(generalMeanRows 1296).c)).2 =
    (161755588053659/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1296).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1296).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1296).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1296

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1296).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1296).criticalRate j.val*(generalMeanRows 1296).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1296).c*(generalMeanRows 1296).criticalPoint j.val)).2-
      (generalMeanRows 1296).J/2-(generalMeanRows 1296).error (generalMeanGrid j.val)+
      (generalMeanRows 1296).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1296).c)).2-
      (generalMeanRows 1296).J/2-(generalMeanRows 1296).error 4 := by
  have he : (generalMeanRows 1296).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1296) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1296)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1296

/-! Kernel-checked entropy margins for general spectral rectangle 1297. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1297
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4605060154, 4469865415, 4339295780, 4213141862, 4091207996, 3973310993, 3859279024, 3748950641, 3642173903, 3538805588, 3438710503, 3341760850, 3247835664, 3156820307, 3068606006, 2983089434, 2900172338, 2819761192, 2741766882, 2666104424, 2592692697, 2521454206, 2452314863, 2385203780, 2320053085, 2256797748, 2195375421, 2135726294, 2077792953, 2021520254, 1966855208, 1913746868, 1862146225, 1812006115, 1763281128, 1715927525, 1669903157, 1625167393, 1581681051, 1539406332, 1498306759, 1458347119, 1419493409, 1381712782, 1344973505, 1309244904, 1274497327, 1240702102, 1207831495, 1175858674, 1144757678, 1114503375, 1085071438, 1056438312, 1028581184, 1001477956, 975107219, 949448230, 924480883, 900185691, 876543763, 853536782, 831146985, 809357145, 788150551, 767510993, 747422742, 727870537, 708839566, 690315455, 672284250, 654732405, 637646770, 621014575, 604823421, 589061266, 573716416, 558777510, 544233514, 530073709, 516287679, 502865306, 489796758, 477072480, 464683186, 452619853, 440873710, 429436230, 418299127, 407454346, 396894053, 386610634, 376596686, 366845012, 357348610, 348100675, 339094588, 330323910, 321782383, 313463916, 305362588, 297472637, 289788460, 282304607, 275015774, 267916804, 261002678, 254268513, 247709559, 241321194, 235098921, 229038364, 223135265, 217385481, 211784980, 206329838, 201016237, 195840461, 190798893, 185888013, 181104396]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1297).prefactor = (4049132610671703/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1297).cutoff/(generalMeanRows 1297).c)).2 =
    (1794534592920047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1297).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1297).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1297).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1297

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1297).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1297).criticalRate j.val*(generalMeanRows 1297).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1297).c*(generalMeanRows 1297).criticalPoint j.val)).2-
      (generalMeanRows 1297).J/2-(generalMeanRows 1297).error (generalMeanGrid j.val)+
      (generalMeanRows 1297).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1297).c)).2-
      (generalMeanRows 1297).J/2-(generalMeanRows 1297).error 4 := by
  have he : (generalMeanRows 1297).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1297) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1297)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1297

/-! Kernel-checked entropy margins for general spectral rectangle 1298. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1298
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5489482641, 5328464102, 5172951873, 5022696424, 4877464648, 4737038351, 4601212917, 4469796116, 4342607061, 4219475266, 4100239813, 3984748595, 3872857649, 3764430544, 3659337833, 3557456558, 3458669797, 3362866254, 3269939890, 3179789574, 3092318779, 3007435291, 2925050948, 2845081399, 2767445878, 2692067005, 2618870589, 2547785457, 2478743291, 2411678470, 2346527940, 2283231072, 2221729548, 2161967242, 2103890115, 2047446115, 1992585084, 1939258670, 1887420241, 1837024816, 1788028981, 1740390829, 1694069891, 1649027078, 1605224617, 1562626004, 1521195946, 1480900315, 1441706103, 1403581374, 1366495222, 1330417738, 1295319962, 1261173855, 1227952262, 1195628877, 1164178216, 1133575583, 1103797046, 1074819404, 1046620169, 1019177531, 992470344, 966478098, 941180896, 916559439, 892595000, 869269405, 846565020, 824464728, 802951914, 782010448, 761624670, 741779373, 722459792, 703651587, 685340830, 667513991, 650157930, 633259879, 616807434, 600788543, 585191495, 570004910, 555217727, 540819197, 526798871, 513146596, 499852497, 486906979, 474300711, 462024621, 450069890, 438427941, 427090436, 416049263, 405296538, 394824589, 384625957, 374693387, 365019821, 355598394, 346422430, 337485433, 328781083, 320303232, 312045901, 304003269, 296169676, 288539611, 281107717, 273868775, 266817712, 259949588, 253259597, 246743062, 240395431, 234212274, 228189280, 222322251, 216607105]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1298).prefactor = (493315625311101/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1298).cutoff/(generalMeanRows 1298).c)).2 =
    (1530213870381441/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1298).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1298).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1298).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1298

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1298).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1298).criticalRate j.val*(generalMeanRows 1298).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1298).c*(generalMeanRows 1298).criticalPoint j.val)).2-
      (generalMeanRows 1298).J/2-(generalMeanRows 1298).error (generalMeanGrid j.val)+
      (generalMeanRows 1298).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1298).c)).2-
      (generalMeanRows 1298).J/2-(generalMeanRows 1298).error 4 := by
  have he : (generalMeanRows 1298).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1298) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1298)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1298

/-! Kernel-checked entropy margins for general spectral rectangle 1299. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1299
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6814161585, 6642594510, 6476348923, 6315186734, 6158886129, 6007240030, 5860054722, 5717148650, 5578351351, 5443502504, 5312451079, 5185054584, 5061178379, 4940695074, 4823483971, 4709430570, 4598426122, 4490367215, 4385155409, 4282696897, 4182902195, 4085685863, 3990966246, 3898665237, 3808708064, 3721023084, 3635541604, 3552197708, 3470928104, 3391671974, 3314370840, 3238968442, 3165410620, 3093645206, 3023621922, 2955292288, 2888609534, 2823528515, 2760005639, 2697998792, 2637467270, 2578371718, 2520674068, 2464337484, 2409326308, 2355606014, 2303143156, 2251905326, 2201861113, 2152980060, 2105232631, 2058590171, 2013024875, 1968509753, 1925018605, 1882525986, 1841007180, 1800438178, 1760795645, 1722056904, 1684199909, 1647203226, 1611046006, 1575707974, 1541169403, 1507411101, 1474414389, 1442161087, 1410633497, 1379814390, 1349686987, 1320234950, 1291442364, 1263293725, 1235773932, 1208868268, 1182562392, 1156842329, 1131694456, 1107105495, 1083062501, 1059552851, 1036564241, 1014084668, 992102428, 970606106, 949584567, 929026949, 908922656, 889261347, 870032936, 851227578, 832835668, 814847830, 797254916, 780047993, 763218345, 746757460, 730657033, 714908950, 699505295, 684438334, 669700517, 655284471, 641182997, 627389064, 613895803, 600696507, 587784626, 575153759, 562797657, 550710213, 538885461, 527317574, 516000859, 504929752, 494098819, 483502749, 473136352, 462994559, 453072414]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1299).prefactor = (635351156442651/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1299).cutoff/(generalMeanRows 1299).c)).2 =
    (795078453174237/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1299).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1299).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1299).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1299

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1299).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1299).criticalRate j.val*(generalMeanRows 1299).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1299).c*(generalMeanRows 1299).criticalPoint j.val)).2-
      (generalMeanRows 1299).J/2-(generalMeanRows 1299).error (generalMeanGrid j.val)+
      (generalMeanRows 1299).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1299).c)).2-
      (generalMeanRows 1299).J/2-(generalMeanRows 1299).error 4 := by
  have he : (generalMeanRows 1299).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1299) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1299)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1299

/-! Kernel-checked entropy margins for general spectral rectangle 1300. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1300
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8174132500, 7995970598, 7822923489, 7654760174, 7491266071, 7332241416, 7177499857, 7026867216, 6880180390, 6737286376, 6598041402, 6462310154, 6329965080, 6200885769, 6074958389, 5952075182, 5832134009, 5715037935, 5600694854, 5489017149, 5379921383, 5273328012, 5169161128, 5067348226, 4967819979, 4870510045, 4775354883, 4682293579, 4591267698, 4502221133, 4415099978, 4329852400, 4246428527, 4164780345, 4084861592, 4006627674, 3930035576, 3855043783, 3781612204, 3709702107, 3639276050, 3570297821, 3502732381, 3436545814, 3371705270, 3308178922, 3245935924, 3184946364, 3125181225, 3066612351, 3009212412, 2952954866, 2897813933, 2843764561, 2790782401, 2738843778, 2687925667, 2638005669, 2589061987, 2541073406, 2494019270, 2447879465, 2402634399, 2358264981, 2314752610, 2272079156, 2230226942, 2189178733, 2148917719, 2109427502, 2070692086, 2032695859, 1995423585, 1958860394, 1922991766, 1887803522, 1853281819, 1819413133, 1786184254, 1753582276, 1721594588, 1690208864, 1659413062, 1629195405, 1599544384, 1570448745, 1541897483, 1513879837, 1486385283, 1459403525, 1432924493, 1406938334, 1381435409, 1356406286, 1331841735, 1307732723, 1284070407, 1260846136, 1238051436, 1215678014, 1193717752, 1172162699, 1151005071, 1130237245, 1109851755, 1089841291, 1070198690, 1050916939, 1031989166, 1013408642, 995168771, 977263094, 959685280, 942429127, 925488559, 908857619, 892530471, 876501397, 860764789, 845315154, 830147107]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1300).prefactor = (1047400429340161/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1300).cutoff/(generalMeanRows 1300).c)).2 =
    (1641653432115649/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1300).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1300).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1300).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1300

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1300).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1300).criticalRate j.val*(generalMeanRows 1300).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1300).c*(generalMeanRows 1300).criticalPoint j.val)).2-
      (generalMeanRows 1300).J/2-(generalMeanRows 1300).error (generalMeanGrid j.val)+
      (generalMeanRows 1300).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1300).c)).2-
      (generalMeanRows 1300).J/2-(generalMeanRows 1300).error 4 := by
  have he : (generalMeanRows 1300).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1300) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1300)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1300

/-! Kernel-checked entropy margins for general spectral rectangle 1301. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1301
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5822833402, 5671088894, 5524148469, 5381797292, 5243835027, 5110074473, 4980340370, 4854468337, 4732303924, 4613701776, 4498524882, 4386643898, 4277936551, 4172287088, 4069585791, 3969728533, 3872616377, 3778155208, 3686255410, 3596831554, 3509802132, 3425089297, 3342618636, 3262318959, 3184122101, 3107962745, 3033778256, 2961508525, 2891095835, 2822484722, 2755621858, 2690455938, 2626937574, 2565019197, 2504654969, 2445800694, 2388413739, 2332452963, 2277878644, 2224652415, 2172737204, 2122097173, 2072697666, 2024505159, 1977487209, 1931612410, 1886850353, 1843171580, 1800547548, 1758950596, 1718353904, 1678731468, 1640058062, 1602309214, 1565461172, 1529490886, 1494375974, 1460094703, 1426625965, 1393949254, 1362044645, 1330892778, 1300474831, 1270772510, 1241768025, 1213444079, 1185783846, 1158770961, 1132389501, 1106623974, 1081459303, 1056880815, 1032874227, 1009425635, 986521501, 964148643, 942294225, 920945744, 900091021, 879718196, 859815710, 840372305, 821377008, 802819128, 784688244, 766974203, 749667104, 732757298, 716235379, 700092175, 684318745, 668906369, 653846546, 639130983, 624751596, 610700496, 596969991, 583552578, 570440938, 557627929, 545106584, 532870109, 520911870, 509225397, 497804376, 486642647, 475734196, 465073155, 454653798, 444470535, 434517910, 424790600, 415283406, 405991254, 396909191, 388032383, 379356109, 370875760, 362586838, 354484949, 346565804]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1301).prefactor = (1104072049212821/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1301).cutoff/(generalMeanRows 1301).c)).2 =
    (1828393106218733/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1301).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1301).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1301).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1301

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1301).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1301).criticalRate j.val*(generalMeanRows 1301).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1301).c*(generalMeanRows 1301).criticalPoint j.val)).2-
      (generalMeanRows 1301).J/2-(generalMeanRows 1301).error (generalMeanGrid j.val)+
      (generalMeanRows 1301).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1301).c)).2-
      (generalMeanRows 1301).J/2-(generalMeanRows 1301).error 4 := by
  have he : (generalMeanRows 1301).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1301) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1301)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1301

/-! Kernel-checked entropy margins for general spectral rectangle 1302. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1302
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5997877872, 5841571661, 5690213952, 5543583452, 5401473801, 5263692173, 5130058038, 5000402073, 4874565186, 4752397652, 4633758341, 4518514021, 4406538742, 4297713273, 4191924597, 4089065457, 3989033941, 3891733106, 3797070640, 3704958548, 3615312871, 3528053421, 3443103549, 3360389924, 3279842333, 3201393495, 3124978891, 3050536607, 2978007189, 2907333507, 2838460629, 2771335709, 2705907873, 2642128123, 2579949241, 2519325704, 2460213598, 2402570544, 2346355626, 2291529325, 2238053453, 2185891094, 2135006552, 2085365295, 2036933904, 1989680029, 1943572347, 1898580514, 1854675130, 1811827701, 1770010603, 1729197047, 1689361052, 1650477407, 1612521650, 1575470034, 1539299507, 1503987682, 1469512815, 1435853785, 1402990069, 1370901723, 1339569360, 1308974135, 1279097726, 1249922312, 1221430565, 1193605626, 1166431093, 1139891009, 1113969845, 1088652485, 1063924218, 1039770720, 1016178048, 993132624, 970621223, 948630970, 927149318, 906164050, 885663262, 865635354, 846069025, 826953263, 808277334, 790030777, 772203397, 754785253, 737766656, 721138160, 704890553, 689014854, 673502307, 658344369, 643532712, 629059212, 614915944, 601095181, 587589382, 574391191, 561493434, 548889108, 536571384, 524533595, 512769239, 501271969, 490035591, 479054060, 468321479, 457832090, 447580272, 437560542, 427767545, 418196055, 408840970, 399697309, 390760211, 382024929, 373486827, 365141381, 356984173]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1302).prefactor = (4549049478609437/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1302).cutoff/(generalMeanRows 1302).c)).2 =
    (1828393106218733/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1302).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1302).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1302).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1302

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1302).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1302).criticalRate j.val*(generalMeanRows 1302).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1302).c*(generalMeanRows 1302).criticalPoint j.val)).2-
      (generalMeanRows 1302).J/2-(generalMeanRows 1302).error (generalMeanGrid j.val)+
      (generalMeanRows 1302).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1302).c)).2-
      (generalMeanRows 1302).J/2-(generalMeanRows 1302).error 4 := by
  have he : (generalMeanRows 1302).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1302) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1302)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1302

/-! Kernel-checked entropy margins for general spectral rectangle 1303. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1303
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6636291412, 6476835110, 6322192909, 6172149503, 6026504430, 5885070664, 5747673366, 5614148786, 5484343285, 5358112464, 5235320387, 5115838886, 4999546942, 4886330119, 4776080061, 4668694037, 4564074531, 4462128862, 4362768848, 4265910496, 4171473722, 4079382088, 3989562573, 3901945350, 3816463594, 3733053295, 3651653093, 3572204120, 3494649861, 3418936018, 3345010389, 3272822754, 3202324771, 3133469876, 3066213191, 3000511442, 2936322876, 2873607190, 2812325460, 2752440075, 2693914680, 2636714113, 2580804356, 2526152484, 2472726616, 2420495871, 2369430325, 2319500974, 2270679694, 2222939206, 2176253041, 2130595512, 2085941681, 2042267331, 1999548937, 1957763645, 1916889244, 1876904141, 1837787345, 1799518439, 1762077564, 1725445399, 1689603143, 1654532494, 1620215639, 1586635232, 1553774382, 1521616635, 1490145964, 1459346754, 1429203788, 1399702236, 1370827642, 1342565913, 1314903309, 1287826431, 1261322212, 1235377906, 1209981082, 1185119608, 1160781649, 1136955658, 1113630363, 1090794764, 1068438123, 1046549958, 1025120037, 1004138366, 983595190, 963480981, 943786434, 924502459, 905620182, 887130928, 869026228, 851297804, 833937569, 816937622, 800290242, 783987881, 768023167, 752388890, 737078006, 722083629, 707399028, 693017620, 678932973, 665138797, 651628942, 638397395, 625438275, 612745833, 600314446, 588138614, 576212961, 564532225, 553091264, 541885044, 530908643, 520157247, 509626146]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1303).prefactor = (4594184283953321/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1303).cutoff/(generalMeanRows 1303).c)).2 =
    (1858641158974229/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1303).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1303).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1303).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1303

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1303).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1303).criticalRate j.val*(generalMeanRows 1303).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1303).c*(generalMeanRows 1303).criticalPoint j.val)).2-
      (generalMeanRows 1303).J/2-(generalMeanRows 1303).error (generalMeanGrid j.val)+
      (generalMeanRows 1303).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1303).c)).2-
      (generalMeanRows 1303).J/2-(generalMeanRows 1303).error 4 := by
  have he : (generalMeanRows 1303).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1303) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1303)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1303

/-! Kernel-checked entropy margins for general spectral rectangle 1304. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1304
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5705037926, 5546228674, 5392661901, 5244102011, 5100329045, 4961137232, 4826333716, 4695737422, 4569178049, 4446495171, 4327537439, 4212161859, 4100233145, 3991623138, 3886210279, 3783879137, 3684519971, 3588028344, 3494304763, 3403254355, 3314786566, 3228814893, 3145256629, 3064032638, 2985067139, 2908287515, 2833624129, 2761010160, 2690381448, 2621676352, 2554835613, 2489802237, 2426521374, 2364940213, 2305007881, 2246675351, 2189895353, 2134622291, 2080812168, 2028422510, 1977412303, 1927741925, 1879373086, 1832268773, 1786393193, 1741711728, 1698190881, 1655798231, 1614502397, 1574272986, 1535080564, 1496896616, 1459693508, 1423444458, 1388123502, 1353705466, 1320165932, 1287481220, 1255628352, 1224585034, 1194329627, 1164841129, 1136099150, 1108083892, 1080776131, 1054157192, 1028208938, 1002913748, 978254501, 954214560, 930777756, 907928372, 885651134, 863931189, 842754097, 822105819, 801972699, 782341458, 763199180, 744533303, 726331602, 708582188, 691273491, 674394253, 657933521, 641880632, 626225211, 610957159, 596066645, 581544101, 567380210, 553565904, 540092351, 526950956, 514133344, 501631365, 489437078, 477542753, 465940859, 454624061, 443585216, 432817366, 422313732, 412067711, 402072870, 392322943, 382811822, 373533561, 364482362, 355652577, 347038703, 338635378, 330437375, 322439602, 314637096, 307025020, 299598659, 292353420, 285284824, 278388506, 271660212]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1304).prefactor = (2342900897363429/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1304).cutoff/(generalMeanRows 1304).c)).2 =
    (450664097893671/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1304).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1304).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1304).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1304

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1304).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1304).criticalRate j.val*(generalMeanRows 1304).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1304).c*(generalMeanRows 1304).criticalPoint j.val)).2-
      (generalMeanRows 1304).J/2-(generalMeanRows 1304).error (generalMeanGrid j.val)+
      (generalMeanRows 1304).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1304).c)).2-
      (generalMeanRows 1304).J/2-(generalMeanRows 1304).error 4 := by
  have he : (generalMeanRows 1304).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1304) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1304)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1304

/-! Kernel-checked entropy margins for general spectral rectangle 1305. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1305
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6436851521, 6270739980, 6109856073, 5953966104, 5802852187, 5656310763, 5514151287, 5376195070, 5242274249, 5112230867, 4985916057, 4863189302, 4743917783, 4627975781, 4515244143, 4405609801, 4298965331, 4195208559, 4094242198, 3995973516, 3900314041, 3807179284, 3716488483, 3628164380, 3542133000, 3458323463, 3376667800, 3297100785, 3219559784, 3143984614, 3070317406, 2998502486, 2928486257, 2860217099, 2793645265, 2728722788, 2665403399, 2603642442, 2543396801, 2484624828, 2427286275, 2371342235, 2316755079, 2263488403, 2211506977, 2160776692, 2111264517, 2062938452, 2015767489, 1969721572, 1924771559, 1880889186, 1838047037, 1796218506, 1755377774, 1715499774, 1676560166, 1638535313, 1601402252, 1565138672, 1529722894, 1495133845, 1461351040, 1428354560, 1396125037, 1364643631, 1333892017, 1303852366, 1274507329, 1245840021, 1217834010, 1190473300, 1163742316, 1137625894, 1112109268, 1087178055, 1062818249, 1039016203, 1015758625, 993032561, 970825391, 949124817, 927918851, 907195809, 886944305, 867153235, 847811777, 828909377, 810435746, 792380849, 774734900, 757488357, 740631910, 724156481, 708053212, 692313463, 676928805, 661891014, 647192065, 632824129, 618779565, 605050917, 591630909, 578512439, 565688576, 553152555, 540897773, 528917783, 517206292, 505757159, 494564386, 483622118, 472924639, 462466367, 452241853, 442245774, 432472935, 422918262, 413576798, 404443705, 395514257]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1305).prefactor = (1206666280654373/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1305).cutoff/(generalMeanRows 1305).c)).2 =
    (183212445383159/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1305).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1305).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1305).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1305

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1305).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1305).criticalRate j.val*(generalMeanRows 1305).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1305).c*(generalMeanRows 1305).criticalPoint j.val)).2-
      (generalMeanRows 1305).J/2-(generalMeanRows 1305).error (generalMeanGrid j.val)+
      (generalMeanRows 1305).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1305).c)).2-
      (generalMeanRows 1305).J/2-(generalMeanRows 1305).error 4 := by
  have he : (generalMeanRows 1305).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1305) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1305)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1305

/-! Kernel-checked entropy margins for general spectral rectangle 1306. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1306
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7604257819, 7431210740, 7263238171, 7100112333, 6941621383, 6787567884, 6637767460, 6492047607, 6350246634, 6212212723, 6077803091, 5946883242, 5819326289, 5695012358, 5573828038, 5455665891, 5340424012, 5228005620, 5118318699, 5011275661, 4906793049, 4804791254, 4705194264, 4607929439, 4512927287, 4420121280, 4329447669, 4240845318, 4154255553, 4069622022, 3986890563, 3906009081, 3826927441, 3749597360, 3673972309, 3600007429, 3527659437, 3456886558, 3387648444, 3319906111, 3253621868, 3188759263, 3125283026, 3063159012, 3002354155, 2942836418, 2884574752, 2827539052, 2771700119, 2717029624, 2663500069, 2611084757, 2559757761, 2509493894, 2460268677, 2412058319, 2364839686, 2318590278, 2273288210, 2228912185, 2185441476, 2142855904, 2101135824, 2060262100, 2020216095, 1980979648, 1942535063, 1904865092, 1867952922, 1831782158, 1796336814, 1761601298, 1727560398, 1694199277, 1661503454, 1629458797, 1598051515, 1567268143, 1537095535, 1507520857, 1478531573, 1450115443, 1422260508, 1394955087, 1368187768, 1341947400, 1316223086, 1291004177, 1266280264, 1242041173, 1218276960, 1194977899, 1172134486, 1149737422, 1127777619, 1106246186, 1085134428, 1064433840, 1044136104, 1024233080, 1004716808, 985579497, 966813525, 948411435, 930365929, 912669863, 895316248, 878298243, 861609151, 845242417, 829191626, 813450495, 798012875, 782872747, 768024215, 753461507, 739178973, 725171078, 711432403, 697957641, 684741594]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1306).prefactor = (4971763046424399/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1306).cutoff/(generalMeanRows 1306).c)).2 =
    (1878021610523893/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1306).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1306).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1306).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1306

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1306).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1306).criticalRate j.val*(generalMeanRows 1306).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1306).c*(generalMeanRows 1306).criticalPoint j.val)).2-
      (generalMeanRows 1306).J/2-(generalMeanRows 1306).error (generalMeanGrid j.val)+
      (generalMeanRows 1306).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1306).c)).2-
      (generalMeanRows 1306).J/2-(generalMeanRows 1306).error 4 := by
  have he : (generalMeanRows 1306).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1306) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1306)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1306

/-! Kernel-checked entropy margins for general spectral rectangle 1307. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1307
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8390227716, 8212103740, 8039029475, 7870776342, 7707132042, 7547898990, 7392892917, 7241941653, 7094884032, 6951568925, 6811854383, 6675606857, 6542700515, 6413016618, 6286442962, 6162873377, 6042207266, 5924349200, 5809208539, 5696699093, 5586738816, 5479249517, 5374156608, 5271388866, 5170878215, 5072559530, 4976370451, 4882251220, 4790144519, 4699995332, 4611750813, 4525360159, 4440774502, 4357946798, 4276831735, 4197385637, 4119566383, 4043333324, 3968647215, 3895470140, 3823765451, 3753497708, 3684632621, 3617136998, 3550978695, 3486126569, 3422550434, 3360221020, 3299109935, 3239189625, 3180433343, 3122815115, 3066309708, 3010892600, 2956539958, 2903228602, 2850935989, 2799640186, 2749319844, 2699954184, 2651522970, 2604006493, 2557385552, 2511641438, 2466755914, 2422711200, 2379489962, 2337075291, 2295450692, 2254600075, 2214507732, 2175158337, 2136536924, 2098628883, 2061419945, 2024896174, 1989043956, 1953849989, 1919301277, 1885385118, 1852089095, 1819401072, 1787309182, 1755801822, 1724867645, 1694495554, 1664674691, 1635394438, 1606644404, 1578414422, 1550694543, 1523475029, 1496746351, 1470499179, 1444724380, 1419413013, 1394556323, 1370145736, 1346172857, 1322629464, 1299507502, 1276799084, 1254496481, 1232592123, 1211078593, 1189948622, 1169195091, 1148811020, 1128789571, 1109124041, 1089807862, 1070834594, 1052197927, 1033891672, 1015909766, 998246261, 980895327, 963851248, 947108418, 930661343, 914504632]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1307).prefactor = (1024244573088859/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1307).cutoff/(generalMeanRows 1307).c)).2 =
    (1901785104976077/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1307).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1307).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1307).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1307

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1307).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1307).criticalRate j.val*(generalMeanRows 1307).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1307).c*(generalMeanRows 1307).criticalPoint j.val)).2-
      (generalMeanRows 1307).J/2-(generalMeanRows 1307).error (generalMeanGrid j.val)+
      (generalMeanRows 1307).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1307).c)).2-
      (generalMeanRows 1307).J/2-(generalMeanRows 1307).error 4 := by
  have he : (generalMeanRows 1307).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1307) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1307)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1307

/-! Kernel-checked entropy margins for general spectral rectangle 1308. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1308
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8515406308, 8334624799, 8158968340, 7988204943, 7822119141, 7660510399, 7503191703, 7349988311, 7200736653, 7055283347, 6913484323, 6775204042, 6640314795, 6508696070, 6380233990, 6254820800, 6132354402, 6012737945, 5895879434, 5781691396, 5670090558, 5560997565, 5454336715, 5350035722, 5248025496, 5148239938, 5050615760, 4955092310, 4861611416, 4770117243, 4680556153, 4592876588, 4507028949, 4422965492, 4340640227, 4260008827, 4181028543, 4103658120, 4027857726, 3953588880, 3880814388, 3809498281, 3739605757, 3671103128, 3603957772, 3538138080, 3473613416, 3410354074, 3348331237, 3287516942, 3227884042, 3169406175, 3112057731, 3055813824, 3000650263, 2946543525, 2893470729, 2841409614, 2790338515, 2740236340, 2691082553, 2642857151, 2595540646, 2549114049, 2503558852, 2458857010, 2414990930, 2371943450, 2329697830, 2288237739, 2247547236, 2207610765, 2168413137, 2129939524, 2092175445, 2055106755, 2018719637, 1983000592, 1947936428, 1913514254, 1879721468, 1846545754, 1813975067, 1781997631, 1750601929, 1719776699, 1689510922, 1659793820, 1630614848, 1601963687, 1573830239, 1546204622, 1519077163, 1492438395, 1466279047, 1440590045, 1415362504, 1390587722, 1366257178, 1342362527, 1318895596, 1295848377, 1273213029, 1250981868, 1229147365, 1207702144, 1186638979, 1165950786, 1145630626, 1125671695, 1106067327, 1086810986, 1067896268, 1049316892, 1031066703, 1013139666, 995529863, 978231494, 961238869, 944546410, 928148648]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1308).prefactor = (1299407327491997/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1308).cutoff/(generalMeanRows 1308).c)).2 =
    (1901785104976077/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1308).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1308).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1308).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1308

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1308).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1308).criticalRate j.val*(generalMeanRows 1308).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1308).c*(generalMeanRows 1308).criticalPoint j.val)).2-
      (generalMeanRows 1308).J/2-(generalMeanRows 1308).error (generalMeanGrid j.val)+
      (generalMeanRows 1308).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1308).c)).2-
      (generalMeanRows 1308).J/2-(generalMeanRows 1308).error 4 := by
  have he : (generalMeanRows 1308).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1308) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1308)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1308

/-! Kernel-checked entropy margins for general spectral rectangle 1309. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1309
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6348042662, 6191104180, 6038980824, 5891457420, 5748333517, 5609421989, 5474547813, 5343546977, 5216265519, 5092558665, 4972290060, 4855331083, 4741560232, 4630862567, 4523129212, 4418256902, 4316147577, 4216708009, 4119849466, 4025487407, 3933541198, 3843933863, 3756591842, 3671444783, 3588425342, 3507468999, 3428513898, 3351500686, 3276372375, 3203074207, 3131553533, 3061759703, 2993643954, 2927159318, 2862260530, 2798903938, 2737047429, 2676650355, 2617673459, 2560078813, 2503829757, 2448890842, 2395227773, 2342807363, 2291597483, 2241567016, 2192685817, 2144924673, 2098255261, 2052650118, 2008082603, 1964526867, 1921957823, 1880351114, 1839683090, 1799930778, 1761071859, 1723084647, 1685948059, 1649641604, 1614145354, 1579439927, 1545506472, 1512326645, 1479882598, 1448156958, 1417132815, 1386793704, 1357123595, 1328106872, 1299728329, 1271973151, 1244826904, 1218275522, 1192305297, 1166902871, 1142055220, 1117749647, 1093973773, 1070715528, 1047963138, 1025705124, 1003930285, 982627697, 961786702, 941396901, 921448146, 901930535, 882834405, 864150324, 845869084, 827981700, 810479398, 793353612, 776595979, 760198334, 744152703, 728451297, 713086513, 698050923, 683337272, 668938473, 654847604, 641057902, 627562762, 614355728, 601430495, 588780899, 576400921, 564284676, 552426415, 540820520, 529461497, 518343981, 507462726, 496812604, 486388604, 476185826, 466199482, 456424891, 446857475]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1309).prefactor = (1107121461720833/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1309).cutoff/(generalMeanRows 1309).c)).2 =
    (1108447755588379/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1309).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1309).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1309).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1309

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1309).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1309).criticalRate j.val*(generalMeanRows 1309).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1309).c*(generalMeanRows 1309).criticalPoint j.val)).2-
      (generalMeanRows 1309).J/2-(generalMeanRows 1309).error (generalMeanGrid j.val)+
      (generalMeanRows 1309).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1309).c)).2-
      (generalMeanRows 1309).J/2-(generalMeanRows 1309).error 4 := by
  have he : (generalMeanRows 1309).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1309) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1309)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1309

/-! Kernel-checked entropy margins for general spectral rectangle 1310. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1310
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6339041696, 6180752642, 6027348372, 5878610619, 5734336008, 5594334651, 5458428907, 5326452281, 5198248453, 5073670405, 4952579650, 4834845535, 4720344616, 4608960104, 4500581355, 4395103413, 4292426601, 4192456144, 4095101827, 4000277688, 3907901730, 3817895669, 3730184690, 3644697237, 3561364806, 3480121766, 3400905191, 3323654700, 3248312313, 3174822322, 3103131161, 3033187297, 2964941119, 2898344840, 2833352405, 2769919406, 2708002998, 2647561826, 2588555955, 2530946801, 2474697074, 2419770714, 2366132842, 2313749704, 2262588625, 2212617962, 2163807064, 2116126226, 2069546655, 2024040434, 1979580481, 1936140526, 1893695073, 1852219372, 1811689393, 1772081798, 1733373917, 1695543720, 1658569801, 1622431351, 1587108137, 1552580485, 1518829261, 1485835849, 1453582138, 1422050504, 1391223792, 1361085303, 1331618781, 1302808396, 1274638729, 1247094766, 1220161878, 1193825814, 1168072688, 1142888969, 1118261467, 1094177326, 1070624016, 1047589318, 1025061320, 1003028404, 981479243, 960402787, 939788258, 919625143, 899903184, 880612376, 861742953, 843285387, 825230380, 807568857, 790291960, 773391044, 756857668, 740683594, 724860777, 709381364, 694237687, 679422258, 664927764, 650747065, 636873186, 623299317, 610018803, 597025147, 584312001, 571873163, 559702576, 547794320, 536142614, 524741807, 513586380, 502670939, 491990211, 481539048, 471312415, 461305393, 451513175, 441931061, 432554460]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1310).prefactor = (2235887868205651/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1310).cutoff/(generalMeanRows 1310).c)).2 =
    (1106595901619637/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1310).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1310).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1310).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1310

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1310).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1310).criticalRate j.val*(generalMeanRows 1310).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1310).c*(generalMeanRows 1310).criticalPoint j.val)).2-
      (generalMeanRows 1310).J/2-(generalMeanRows 1310).error (generalMeanGrid j.val)+
      (generalMeanRows 1310).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1310).c)).2-
      (generalMeanRows 1310).J/2-(generalMeanRows 1310).error 4 := by
  have he : (generalMeanRows 1310).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1310) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1310)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1310

/-! Kernel-checked entropy margins for general spectral rectangle 1311. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1311
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5531677526, 5374350159, 5222290657, 5075261674, 4933041533, 4795422785, 4662210935, 4533223311, 4408288063, 4287243263, 4169936104, 4056222183, 3945964853, 3839034643, 3735308728, 3634670456, 3537008915, 3442218540, 3350198756, 3260853651, 3174091675, 3089825372, 3007971122, 2928448917, 2851182143, 2776097385, 2703124250, 2632195194, 2563245368, 2496212476, 2431036640, 2367660274, 2306027969, 2246086386, 2187784151, 2131071765, 2075901511, 2022227373, 1970004960, 1919191427, 1869745413, 1821626971, 1774797507, 1729219727, 1684857576, 1641676192, 1599641854, 1558721936, 1518884866, 1480100081, 1442337989, 1405569934, 1369768155, 1334905757, 1300956679, 1267895658, 1235698205, 1204340575, 1173799742, 1144053371, 1115079795, 1086857990, 1059367559, 1032588701, 1006502200, 981089397, 956332179, 932212957, 908714646, 885820655, 863514867, 841781624, 820605711, 799972348, 779867166, 760276206, 741185895, 722583042, 704454824, 686788771, 669572761, 652795006, 636444042, 620508721, 604978199, 589841930, 575089653, 560711390, 546697429, 533038326, 519724888, 506748172, 494099476, 481770329, 469752491, 458037939, 446618866, 435487673, 424636962, 414059534, 403748379, 393696672, 383897770, 374345206, 365032680, 355954062, 347103381, 338474822, 330062724, 321861574, 313866002, 306070779, 298470812, 291061142, 283836937, 276793492, 269926223, 263230667, 256702474, 250337408, 244131343]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1311).prefactor = (4559629170369321/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1311).cutoff/(generalMeanRows 1311).c)).2 =
    (1081365323979713/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1311).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1311).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1311).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1311

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1311).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1311).criticalRate j.val*(generalMeanRows 1311).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1311).c*(generalMeanRows 1311).criticalPoint j.val)).2-
      (generalMeanRows 1311).J/2-(generalMeanRows 1311).error (generalMeanGrid j.val)+
      (generalMeanRows 1311).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1311).c)).2-
      (generalMeanRows 1311).J/2-(generalMeanRows 1311).error 4 := by
  have he : (generalMeanRows 1311).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1311) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1311)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1311

/-! Kernel-checked entropy margins for general spectral rectangle 1312. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1312
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6294562375, 6129576860, 5969833126, 5815096718, 5665148973, 5519785547, 5378815106, 5242058175, 5109346107, 4980520172, 4855430735, 4733936529, 4615903995, 4501206688, 4389724751, 4281344422, 4175957606, 4073461474, 3973758101, 3876754142, 3782360523, 3690492177, 3601067784, 3514009542, 3429242957, 3346696644, 3266302150, 3187993783, 3111708461, 3037385569, 2964966826, 2894396161, 2825619600, 2758585158, 2693242741, 2629544052, 2567442504, 2506893142, 2447852563, 2390278845, 2334131482, 2279371322, 2225960503, 2173862403, 2123041581, 2073463734, 2025095647, 1977905146, 1931861062, 1886933187, 1843092237, 1800309816, 1758558386, 1717811229, 1678042419, 1639226795, 1601339930, 1564358107, 1528258290, 1493018106, 1458615817, 1425030300, 1392241026, 1360228040, 1328971942, 1298453867, 1268655470, 1239558907, 1211146822, 1183402326, 1156308987, 1129850815, 1104012244, 1078778127, 1054133713, 1030064645, 1006556939, 983596981, 961171509, 939267607, 917872694, 896974513, 876561123, 856620886, 837142466, 818114813, 799527158, 781369006, 763630124, 746300541, 729370533, 712830621, 696671563, 680884346, 665460184, 650390505, 635666953, 621281375, 607225821, 593492536, 580073956, 566962700, 554151570, 541633541, 529401762, 517449546, 505770369, 494357865, 483205823, 472308181, 461659022, 451252573, 441083198, 431145399, 421433807, 411943183, 402668411, 393604500, 384746575, 376089880, 367629769]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1312).prefactor = (1173664029315713/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1312).cutoff/(generalMeanRows 1312).c)).2 =
    (54871906823321/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1312).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1312).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1312).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1312

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1312).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1312).criticalRate j.val*(generalMeanRows 1312).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1312).c*(generalMeanRows 1312).criticalPoint j.val)).2-
      (generalMeanRows 1312).J/2-(generalMeanRows 1312).error (generalMeanGrid j.val)+
      (generalMeanRows 1312).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1312).c)).2-
      (generalMeanRows 1312).J/2-(generalMeanRows 1312).error 4 := by
  have he : (generalMeanRows 1312).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1312) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1312)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1312

/-! Kernel-checked entropy margins for general spectral rectangle 1313. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1313
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7408699275, 7236575232, 7069553530, 6907405542, 6749918542, 6596894191, 6448147191, 6303504110, 6162802319, 6025889064, 5892620629, 5762861586, 5636484128, 5513367468, 5393397294, 5276465282, 5162468651, 5051309764, 4942895761, 4837138230, 4733952903, 4633259381, 4534980882, 4439044008, 4345378534, 4253917213, 4164595596, 4077351869, 3992126695, 3908863078, 3827506230, 3748003452, 3670304016, 3594359069, 3520121528, 3447545995, 3376588670, 3307207271, 3239360965, 3173010295, 3108117117, 3044644538, 2982556863, 2921819536, 2862399097, 2804263128, 2747380211, 2691719890, 2637252624, 2583949756, 2531783473, 2480726778, 2430753452, 2381838029, 2333955765, 2287082610, 2241195187, 2196270763, 2152287226, 2109223066, 2067057352, 2025769711, 1985340312, 1945749844, 1906979500, 1869010962, 1831826382, 1795408370, 1759739978, 1724804684, 1690586381, 1657069364, 1624238318, 1592078304, 1560574749, 1529713437, 1499480493, 1469862380, 1440845885, 1412418108, 1384566459, 1357278643, 1330542656, 1304346774, 1278679547, 1253529791, 1228886581, 1204739244, 1181077351, 1157890713, 1135169371, 1112903594, 1091083869, 1069700901, 1048745599, 1028209079, 1008082655, 988357833, 969026308, 950079958, 931510843, 913311192, 895473411, 877990067, 860853891, 844057773, 827594755, 811458033, 795640947, 780136981, 764939760, 750043046, 735440733, 721126847, 707095539, 693341088, 679857892, 666640467, 653683447, 640981578, 628529717]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1313).prefactor = (4833681695559543/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1313).cutoff/(generalMeanRows 1313).c)).2 =
    (1119705266772197/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1313).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1313).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1313).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1313

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1313).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1313).criticalRate j.val*(generalMeanRows 1313).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1313).c*(generalMeanRows 1313).criticalPoint j.val)).2-
      (generalMeanRows 1313).J/2-(generalMeanRows 1313).error (generalMeanGrid j.val)+
      (generalMeanRows 1313).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1313).c)).2-
      (generalMeanRows 1313).J/2-(generalMeanRows 1313).error 4 := by
  have he : (generalMeanRows 1313).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1313) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1313)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1313

/-! Kernel-checked entropy margins for general spectral rectangle 1314. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1314
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8436221673, 8259094045, 8086962672, 7919601017, 7756798726, 7598360058, 7444102509, 7293855586, 7147459732, 7004765355, 6865631977, 6729927463, 6597527338, 6468314164, 6342176991, 6219010851, 6098716312, 5981199059, 5866369532, 5754142581, 5644437161, 5537176052, 5432285601, 5329695489, 5229338514, 5131150396, 5035069594, 4941037139, 4848996480, 4758893343, 4670675598, 4584293140, 4499697772, 4416843105, 4335684458, 4256178769, 4178284511, 4101961613, 4027171387, 3953876460, 3882040710, 3811629207, 3742608155, 3674944843, 3608607591, 3543565708, 3479789448, 3417249965, 3355919278, 3295770237, 3236776481, 3178912414, 3122153168, 3066474577, 3011853151, 2958266046, 2905691042, 2854106520, 2803491438, 2753825311, 2705088191, 2657260649, 2610323753, 2564259056, 2519048575, 2474674777, 2431120567, 2388369266, 2346404608, 2305210715, 2264772095, 2225073623, 2186100534, 2147838408, 2110273163, 2073391042, 2037178607, 2001622725, 1966710562, 1932429575, 1898767502, 1865712353, 1833252405, 1801376195, 1770072509, 1739330379, 1709139075, 1679488097, 1650367174, 1621766251, 1593675487, 1566085252, 1538986117, 1512368851, 1486224415, 1460543960, 1435318818, 1410540501, 1386200696, 1362291258, 1338804210, 1315731736, 1293066179, 1270800034, 1248925950, 1227436721, 1206325285, 1185584722, 1165208248, 1145189213, 1125521097, 1106197512, 1087212191, 1068558991, 1050231888, 1032224978, 1014532467, 997148675, 980068034, 963285078, 946794449]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1314).prefactor = (19440719996303/3906250000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1314).cutoff/(generalMeanRows 1314).c)).2 =
    (2274163065535233/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1314).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1314).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1314).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1314

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1314).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1314).criticalRate j.val*(generalMeanRows 1314).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1314).c*(generalMeanRows 1314).criticalPoint j.val)).2-
      (generalMeanRows 1314).J/2-(generalMeanRows 1314).error (generalMeanGrid j.val)+
      (generalMeanRows 1314).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1314).c)).2-
      (generalMeanRows 1314).J/2-(generalMeanRows 1314).error 4 := by
  have he : (generalMeanRows 1314).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1314) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1314)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1314

/-! Kernel-checked entropy margins for general spectral rectangle 1315. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1315
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8589268852, 8406792242, 8229490358, 8057128995, 7889490627, 7726372795, 7567586685, 7412955872, 7262315207, 7115509825, 6972394262, 6832831663, 6696693077, 6563856823, 6434207914, 6307637542, 6184042616, 6063325335, 5945392805, 5830156696, 5717532918, 5607441337, 5499805507, 5394552431, 5291612337, 5190918477, 5092406937, 4996016468, 4901688321, 4809366110, 4718995667, 4630524922, 4543903786, 4459084041, 4376019241, 4294664620, 4214977002, 4136914726, 4060437561, 3985506646, 3912084416, 3840134544, 3769621882, 3700512409, 3632773175, 3566372258, 3501278719, 3437462553, 3374894659, 3313546794, 3253391542, 3194402277, 3136553136, 3079818986, 3024175394, 2969598602, 2916065504, 2863553617, 2812041059, 2761506532, 2711929293, 2663289141, 2615566397, 2568741882, 2522796904, 2477713241, 2433473124, 2390059222, 2347454631, 2305642855, 2264607799, 2224333751, 2184805375, 2146007694, 2107926086, 2070546266, 2033854282, 1997836501, 1962479602, 1927770569, 1893696675, 1860245483, 1827404830, 1795162826, 1763507842, 1732428504, 1701913688, 1671952508, 1642534318, 1613648699, 1585285455, 1557434607, 1530086390, 1503231242, 1476859806, 1450962919, 1425531609, 1400557091, 1376030763, 1351944198, 1328289145, 1305057520, 1282241406, 1259833044, 1237824836, 1216209334, 1194979242, 1174127410, 1153646831, 1133530639, 1113772103, 1094364626, 1075301741, 1056577111, 1038184520, 1020117877, 1002371209, 984938660, 967814488, 950993061, 934468859]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1315).prefactor = (2562102954097791/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1315).cutoff/(generalMeanRows 1315).c)).2 =
    (45404829837641/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1315).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1315).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1315).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1315

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1315).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1315).criticalRate j.val*(generalMeanRows 1315).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1315).c*(generalMeanRows 1315).criticalPoint j.val)).2-
      (generalMeanRows 1315).J/2-(generalMeanRows 1315).error (generalMeanGrid j.val)+
      (generalMeanRows 1315).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1315).c)).2-
      (generalMeanRows 1315).J/2-(generalMeanRows 1315).error 4 := by
  have he : (generalMeanRows 1315).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1315) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1315)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1315

/-! Kernel-checked entropy margins for general spectral rectangle 1316. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1316
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![6348800949, 6185036750, 6026424852, 5872734940, 5723752279, 5579276253, 5439119071, 5303104629, 5171067492, 5042851990, 4918311410, 4797307270, 4679708675, 4565391728, 4454239003, 4346139071, 4240986067, 4138679299, 4039122892, 3942225461, 3847899818, 3756062700, 3666634520, 3579539140, 3494703662, 3412058235, 3331535876, 3253072310, 3176605812, 3102077073, 3029429065, 2958606922, 2889557829, 2822230914, 2756577153, 2692549275, 2630101685, 2569190374, 2509772853, 2451808077, 2395256384, 2340079430, 2286240133, 2233702618, 2182432163, 2132395155, 2083559042, 2035892287, 1989364331, 1943945554, 1899607234, 1856321517, 1814061383, 1772800612, 1732513756, 1693176111, 1654763689, 1617253193, 1580621991, 1544848095, 1509910136, 1475787347, 1442459536, 1409907073, 1378110865, 1347052346, 1316713453, 1287076612, 1258124724, 1229841147, 1202209683, 1175214565, 1148840441, 1123072366, 1097895782, 1073296515, 1049260756, 1025775055, 1002826307, 980401746, 958488929, 937075734, 916150343, 895701241, 875717199, 856187275, 837100798, 818447364, 800216830, 782399304, 764985138, 747964924, 731329485, 715069869, 699177346, 683643395, 668459708, 653618175, 639110886, 624930119, 611068344, 597518207, 584272535, 571324325, 558666745, 546293122, 534196946, 522371862, 510811664, 499510295, 488461843, 477660533, 467100729, 456776928, 446683754, 436815961, 427168423, 417736139, 408514220, 399497894, 390682501]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1316).prefactor = (4536809760579443/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1316).cutoff/(generalMeanRows 1316).c)).2 =
    (571393055111133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1316).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1316).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1316).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1316

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1316).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1316).criticalRate j.val*(generalMeanRows 1316).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1316).c*(generalMeanRows 1316).criticalPoint j.val)).2-
      (generalMeanRows 1316).J/2-(generalMeanRows 1316).error (generalMeanGrid j.val)+
      (generalMeanRows 1316).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1316).c)).2-
      (generalMeanRows 1316).J/2-(generalMeanRows 1316).error 4 := by
  have he : (generalMeanRows 1316).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1316) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1316)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1316

/-! Kernel-checked entropy margins for general spectral rectangle 1317. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1317
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7205040662, 7034900227, 6869847618, 6709655101, 6554110712, 6403016759, 6256188493, 6113452938, 5974647848, 5839620781, 5708228274, 5580335101, 5455813613, 5334543136, 5216409440, 5101304251, 4989124813, 4879773490, 4773157403, 4669188106, 4567781281, 4468856468, 4372336812, 4278148835, 4186222225, 4096489642, 4008886542, 3923351009, 3839823604, 3758247230, 3678566993, 3600730091, 3524685695, 3450384848, 3377780369, 3306826762, 3237480132, 3169698106, 3103439762, 3038665558, 2975337266, 2913417917, 2852871741, 2793664113, 2735761504, 2679131435, 2623742432, 2569563982, 2516566497, 2464721273, 2414000457, 2364377014, 2315824693, 2268317998, 2221832160, 2176343112, 2131827456, 2088262447, 2045625966, 2003896497, 1963053107, 1923075425, 1883943625, 1845638405, 1808140972, 1771433022, 1735496727, 1700314718, 1665870072, 1632146294, 1599127310, 1566797447, 1535141426, 1504144346, 1473791678, 1444069245, 1414963223, 1386460120, 1358546773, 1331210336, 1304438273, 1278218345, 1252538606, 1227387392, 1202753315, 1178625255, 1154992351, 1131843996, 1109169829, 1086959730, 1065203810, 1043892410, 1023016091, 1002565629, 982532010, 962906425, 943680265, 924845113, 906392743, 888315113, 870604360, 853252798, 836252909, 819597345, 803278919, 787290602, 771625521, 756276953, 741238324, 726503202, 712065295, 697918450, 684056646, 670473994, 657164730, 644123218, 631343940, 618821500, 606550614, 594526116, 582742947]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1317).prefactor = (4668265614643833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1317).cutoff/(generalMeanRows 1317).c)).2 =
    (115583074445777/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1317).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1317).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1317).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1317

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1317).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1317).criticalRate j.val*(generalMeanRows 1317).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1317).c*(generalMeanRows 1317).criticalPoint j.val)).2-
      (generalMeanRows 1317).J/2-(generalMeanRows 1317).error (generalMeanGrid j.val)+
      (generalMeanRows 1317).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1317).c)).2-
      (generalMeanRows 1317).J/2-(generalMeanRows 1317).error 4 := by
  have he : (generalMeanRows 1317).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1317) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1317)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1317

/-! Kernel-checked entropy margins for general spectral rectangle 1318. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1318
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8269059248, 8093850421, 7923604191, 7758095863, 7597116758, 7440472658, 7287982446, 7139476896, 6994797609, 6853796053, 6716332722, 6582276373, 6451503348, 6323896966, 6199346970, 6077749034, 5959004315, 5843019050, 5729704181, 5618975030, 5510750987, 5404955238, 5301514505, 5200358820, 5101421310, 5004637999, 4909947631, 4817291506, 4726613323, 4637859043, 4550976759, 4465916572, 4382630483, 4301072290, 4221197485, 4142963175, 4066327989, 3991252007, 3917696683, 3845624783, 3775000313, 3705788468, 3637955573, 3571469031, 3506297273, 3442409714, 3379776711, 3318369519, 3258160253, 3199121855, 3141228058, 3084453351, 3028772955, 2974162789, 2920599444, 2868060158, 2816522789, 2765965797, 2716368216, 2667709638, 2619970188, 2573130510, 2527171746, 2482075518, 2437823916, 2394399477, 2351785174, 2309964399, 2268920952, 2228639025, 2189103192, 2150298396, 2112209937, 2074823463, 2038124956, 2002100728, 1966737402, 1932021914, 1897941493, 1864483660, 1831636218, 1799387242, 1767725073, 1736638310, 1706115806, 1676146654, 1646720188, 1617825972, 1589453796, 1561593670, 1534235816, 1507370665, 1480988851, 1455081205, 1429638752, 1404652703, 1380114453, 1356015576, 1332347819, 1309103101, 1286273504, 1263851273, 1241828813, 1220198680, 1198953582, 1178086375, 1157590057, 1137457767, 1117682782, 1098258510, 1079178492, 1060436398, 1042026020, 1023941275, 1006176197, 988724938, 971581765, 954741055, 938197296, 921945082, 905979111]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1318).prefactor = (2401765226990979/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1318).cutoff/(generalMeanRows 1318).c)).2 =
    (2927104717013437/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1318).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1318).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1318).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1318

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1318).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1318).criticalRate j.val*(generalMeanRows 1318).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1318).c*(generalMeanRows 1318).criticalPoint j.val)).2-
      (generalMeanRows 1318).J/2-(generalMeanRows 1318).error (generalMeanGrid j.val)+
      (generalMeanRows 1318).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1318).c)).2-
      (generalMeanRows 1318).J/2-(generalMeanRows 1318).error 4 := by
  have he : (generalMeanRows 1318).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1318) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1318)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1318

/-! Kernel-checked entropy margins for general spectral rectangle 1319. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1319
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8508658504, 8328372933, 8153193751, 7982889754, 7817246216, 7656063291, 7499154614, 7346346058, 7197474631, 7052387500, 6910941115, 6773000430, 6638438205, 6507134377, 6378975496, 6253854212, 6131668818, 6012322834, 5895724622, 5781787050, 5670427173, 5561565950, 5455127981, 5351041271, 5249237007, 5149649361, 5052215303, 4956874429, 4863568810, 4772242840, 4682843107, 4595318268, 4509618932, 4425697557, 4343508349, 4263007168, 4184151448, 4106900109, 4031213492, 3957053279, 3884382437, 3813165152, 3743366772, 3674953756, 3607893620, 3542154895, 3477707076, 3414520586, 3352566733, 3291817674, 3232246381, 3173826605, 3116532848, 3060340330, 3005224966, 2951163333, 2898132649, 2846110748, 2795076058, 2745007578, 2695884859, 2647687983, 2600397545, 2553994636, 2508460826, 2463778147, 2419929078, 2376896530, 2334663833, 2293214721, 2252533321, 2212604141, 2173412054, 2134942292, 2097180432, 2060112387, 2023724395, 1988003011, 1952935097, 1918507810, 1884708600, 1851525197, 1818945604, 1786958091, 1755551185, 1724713665, 1694434555, 1664703118, 1635508847, 1606841463, 1578690904, 1551047325, 1523901087, 1497242757, 1471063099, 1445353070, 1420103814, 1395306663, 1370953124, 1347034880, 1323543786, 1300471863, 1277811293, 1255554418, 1233693735, 1212221893, 1191131686, 1170416055, 1150068081, 1130080984, 1110448115, 1091162961, 1072219135, 1053610377, 1035330549, 1017373633, 999733730, 982405054, 965381933, 948658805, 932230213]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1319).prefactor = (4942714645446017/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1319).cutoff/(generalMeanRows 1319).c)).2 =
    (2927104717013437/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1319).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1319).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1319).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1319

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1319).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1319).criticalRate j.val*(generalMeanRows 1319).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1319).c*(generalMeanRows 1319).criticalPoint j.val)).2-
      (generalMeanRows 1319).J/2-(generalMeanRows 1319).error (generalMeanGrid j.val)+
      (generalMeanRows 1319).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1319).c)).2-
      (generalMeanRows 1319).J/2-(generalMeanRows 1319).error 4 := by
  have he : (generalMeanRows 1319).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1319) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1319)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1319

/-! Kernel-checked entropy margins for general spectral rectangle 1320. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1320
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8537185583, 8354223656, 8176471239, 8003692854, 7835669753, 7672198304, 7513088569, 7358163040, 7207255530, 7060210171, 6916880534, 6777128837, 6640825232, 6507847172, 6378078836, 6251410610, 6127738623, 6006964322, 5888994084, 5773738875, 5661113923, 5551038434, 5443435324, 5338230976, 5235355022, 5134740130, 5036321826, 4940038314, 4845830320, 4753640942, 4663415518, 4575101496, 4488648320, 4404007318, 4321131608, 4239975996, 4160496894, 4082652239, 4006401413, 3931705176, 3858525599, 3786826000, 3716570887, 3647725904, 3580257779, 3514134275, 3449324147, 3385797098, 3323523737, 3262475544, 3202624834, 3143944720, 3086409086, 3029992551, 2974670446, 2920418782, 2867214229, 2815034085, 2763856262, 2713659254, 2664422124, 2616124479, 2568746454, 2522268691, 2476672326, 2431938966, 2388050682, 2344989985, 2302739817, 2261283538, 2220604907, 2180688076, 2141517576, 2103078301, 2065355503, 2028334778, 1992002058, 1956343597, 1921345968, 1886996046, 1853281008, 1820188316, 1787705716, 1755821226, 1724523129, 1693799969, 1663640539, 1634033878, 1604969263, 1576436203, 1548424434, 1520923910, 1493924801, 1467417486, 1441392547, 1415840765, 1390753115, 1366120759, 1341935046, 1318187502, 1294869830, 1271973903, 1249491763, 1227415611, 1205737812, 1184450882, 1163547492, 1143020459, 1122862746, 1103067457, 1083627835, 1064537256, 1045789230, 1027377396, 1009295517, 991537481, 974097298, 956969092, 940147106, 923625694, 907399320]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1320).prefactor = (1253452964945787/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1320).cutoff/(generalMeanRows 1320).c)).2 =
    (1461643959243369/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1320).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1320).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1320).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1320

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1320).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1320).criticalRate j.val*(generalMeanRows 1320).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1320).c*(generalMeanRows 1320).criticalPoint j.val)).2-
      (generalMeanRows 1320).J/2-(generalMeanRows 1320).error (generalMeanGrid j.val)+
      (generalMeanRows 1320).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1320).c)).2-
      (generalMeanRows 1320).J/2-(generalMeanRows 1320).error 4 := by
  have he : (generalMeanRows 1320).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1320) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1320)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1320

/-! Kernel-checked entropy margins for general spectral rectangle 1321. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1321
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![7613843754, 7446276802, 7283541907, 7125421411, 6971713016, 6822228305, 6676791438, 6535238001, 6397413986, 6263174875, 6132384837, 6004915997, 5880647789, 5759466372, 5641264102, 5525939063, 5413394633, 5303539098, 5196285301, 5091550318, 4989255169, 4889324550, 4791686592, 4696272634, 4603017020, 4511856915, 4422732127, 4335584950, 4250360019, 4167004173, 4085466328, 4005697363, 3927650015, 3851278771, 3776539785, 3703390785, 3631790994, 3561701055, 3493082962, 3425899995, 3360116654, 3295698607, 3232612635, 3170826578, 3110309293, 3051030603, 2992961261, 2936072908, 2880338033, 2825729943, 2772222727, 2719791222, 2668410988, 2618058279, 2568710013, 2520343749, 2472937664, 2426470529, 2380921687, 2336271032, 2292498992, 2249586508, 2207515016, 2166266432, 2125823135, 2086167950, 2047284135, 2009155369, 1971765731, 1935099697, 1899142119, 1863878220, 1829293578, 1795374117, 1762106096, 1729476099, 1697471027, 1666078086, 1635284781, 1605078904, 1575448529, 1546382002, 1517867936, 1489895200, 1462452915, 1435530443, 1409117388, 1383203581, 1357779080, 1332834161, 1308359313, 1284345233, 1260782820, 1237663170, 1214977572, 1192717501, 1170874614, 1149440748, 1128407912, 1107768285, 1087514209, 1067638191, 1048132891, 1028991126, 1010205861, 991770206, 973677417, 955920886, 938494144, 921390853, 904604805, 888129919, 871960240, 856089932, 840513277, 825224675, 810218637, 795489785, 781032851, 766842669, 752914180]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1321).prefactor = (895467245684751/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1321).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1321).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1321).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1321

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1321).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1321).criticalRate j.val*(generalMeanRows 1321).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1321).c*(generalMeanRows 1321).criticalPoint j.val)).2-
      (generalMeanRows 1321).J/2-(generalMeanRows 1321).error (generalMeanGrid j.val)+
      (generalMeanRows 1321).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1321).c)).2-
      (generalMeanRows 1321).J/2-(generalMeanRows 1321).error 4 := by
  have he : (generalMeanRows 1321).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1321) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1321)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1321

/-! Kernel-checked entropy margins for general spectral rectangle 1322. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1322
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8082545395, 7910403385, 7743148658, 7580560102, 7422432339, 7268574207, 7118807421, 6972965385, 6830892144, 6692441446, 6557475911, 6425866285, 6297490774, 6172234442, 6049988674, 5930650688, 5814123095, 5700313502, 5589134148, 5480501578, 5374336345, 5270562732, 5169108508, 5069904695, 4972885363, 4877987436, 4785150515, 4694316717, 4605430522, 4518438639, 4433289874, 4349935015, 4268326719, 4188419412, 4110169195, 4033533754, 3958472280, 3884945391, 3812915062, 3742344556, 3673198368, 3605442156, 3539042697, 3473967831, 3410186411, 3347668262, 3286384134, 3226305668, 3167405352, 3109656489, 3053033162, 2997510204, 2943063165, 2889668287, 2837302475, 2785943272, 2735568836, 2686157915, 2637689826, 2590144437, 2543502142, 2497743847, 2452850951, 2408805327, 2365589309, 2323185673, 2281577627, 2240748790, 2200683188, 2161365230, 2122779706, 2084911768, 2047746923, 2011271020, 1975470239, 1940331084, 1905840371, 1871985219, 1838753042, 1806131539, 1774108690, 1742672743, 1711812207, 1681515850, 1651772686, 1622571970, 1593903194, 1565756078, 1538120563, 1510986808, 1484345185, 1458186269, 1432500836, 1407279858, 1382514497, 1358196100, 1334316196, 1310866489, 1287838857, 1265225344, 1243018158, 1221209670, 1199792402, 1178759033, 1158102387, 1137815436, 1117891293, 1098323208, 1079104568, 1060228893, 1041689830, 1023481154, 1005596763, 988030674, 970777025, 953830067, 937184165, 920833793, 904773535, 888998078, 873502213]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1322).prefactor = (2301662948226827/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1322).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1322).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1322).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1322

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1322).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1322).criticalRate j.val*(generalMeanRows 1322).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1322).c*(generalMeanRows 1322).criticalPoint j.val)).2-
      (generalMeanRows 1322).J/2-(generalMeanRows 1322).error (generalMeanGrid j.val)+
      (generalMeanRows 1322).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1322).c)).2-
      (generalMeanRows 1322).J/2-(generalMeanRows 1322).error 4 := by
  have he : (generalMeanRows 1322).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1322) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1322)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1322

/-! Kernel-checked entropy margins for general spectral rectangle 1323. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1323
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8399125927, 8222230201, 8050331154, 7883202341, 7720633478, 7562428880, 7408406082, 7258394619, 7112234950, 6969777488, 6830881754, 6695415604, 6563254544, 6434281117, 6308384344, 6185459228, 6065406301, 5948131213, 5833544361, 5721560554, 5612098703, 5505081542, 5400435372, 5298089825, 5197977653, 5100034526, 5004198853, 4910411617, 4818616218, 4728758332, 4640785783, 4554648414, 4470297983, 4387688052, 4306773895, 4227512404, 4149862006, 4073782586, 3999235413, 3926183070, 3854589395, 3784419416, 3715639299, 3648216291, 3582118676, 3517315727, 3453777660, 3391475595, 3330381518, 3270468244, 3211709382, 3154079303, 3097553111, 3042106610, 2987716282, 2934359256, 2882013287, 2830656728, 2780268516, 2730828140, 2682315632, 2634711539, 2587996911, 2542153278, 2497162640, 2453007447, 2409670584, 2367135358, 2325385484, 2284405073, 2244178616, 2204690975, 2165927373, 2127873378, 2090514896, 2053838160, 2017829721, 1982476438, 1947765467, 1913684258, 1880220539, 1847362317, 1815097860, 1783415700, 1752304617, 1721753639, 1691752032, 1662289293, 1633355145, 1604939532, 1577032612, 1549624752, 1522706520, 1496268686, 1470302210, 1444798243, 1419748117, 1395143345, 1370975613, 1347236781, 1323918870, 1301014068, 1278514719, 1256413322, 1234702529, 1213375136, 1192424085, 1171842460, 1151623481, 1131760501, 1112247008, 1093076614, 1074243061, 1055740208, 1037562040, 1019702655, 1002156267, 984917202, 967979897, 951338893, 934988839]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1323).prefactor = (2366430420663429/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1323).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1323).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1323).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1323

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1323).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1323).criticalRate j.val*(generalMeanRows 1323).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1323).c*(generalMeanRows 1323).criticalPoint j.val)).2-
      (generalMeanRows 1323).J/2-(generalMeanRows 1323).error (generalMeanGrid j.val)+
      (generalMeanRows 1323).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1323).c)).2-
      (generalMeanRows 1323).J/2-(generalMeanRows 1323).error 4 := by
  have he : (generalMeanRows 1323).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1323) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1323)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1323

/-! Kernel-checked entropy margins for general spectral rectangle 1324. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1324
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8543821738, 8361855467, 8185055400, 8013187805, 7846035583, 7683396663, 7525082585, 7370917245, 7220735788, 7074383614, 6931715505, 6792594829, 6656892840, 6524488045, 6395265628, 6269116942, 6145939041, 6025634256, 5908109821, 5793277518, 5681053363, 5571357320, 5464113034, 5359247592, 5256691301, 5156377485, 5058242298, 4962224553, 4868265563, 4776308994, 4686300732, 4598188754, 4511923017, 4427455346, 4344739336, 4263730259, 4184384976, 4106661857, 4030520708, 3955922697, 3882830288, 3811207183, 3741018263, 3672229530, 3604808061, 3538721958, 3473940304, 3410433119, 3348171322, 3287126692, 3227271834, 3168580142, 3111025774, 3054583614, 2999229250, 2944938943, 2891689603, 2839458767, 2788224572, 2737965735, 2688661533, 2640291781, 2592836817, 2546277479, 2500595094, 2455771454, 2411788808, 2368629842, 2326277669, 2284715809, 2243928182, 2203899096, 2164613228, 2126055620, 2088211665, 2051067094, 2014607973, 1978820684, 1943691924, 1909208690, 1875358276, 1842128257, 1809506490, 1777481099, 1746040472, 1715173252, 1684868330, 1655114838, 1625902146, 1597219850, 1569057771, 1541405948, 1514254630, 1487594273, 1461415536, 1435709272, 1410466525, 1385678528, 1361336693, 1337432611, 1313958047, 1290904933, 1268265368, 1246031610, 1224196075, 1202751334, 1181690106, 1161005258, 1140689797, 1120736875, 1101139775, 1081891917, 1062986851, 1044418254, 1026179928, 1008265795, 990669900, 973386402, 956409574, 939733801, 923353577]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1324).prefactor = (4866040825096007/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1324).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1324).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1324).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1324

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1324).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1324).criticalRate j.val*(generalMeanRows 1324).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1324).c*(generalMeanRows 1324).criticalPoint j.val)).2-
      (generalMeanRows 1324).J/2-(generalMeanRows 1324).error (generalMeanGrid j.val)+
      (generalMeanRows 1324).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1324).c)).2-
      (generalMeanRows 1324).J/2-(generalMeanRows 1324).error 4 := by
  have he : (generalMeanRows 1324).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1324) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1324)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1324

/-! Kernel-checked entropy margins for general spectral rectangle 1325. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1325
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8263043194, 8090652353, 7923110356, 7760197127, 7601708335, 7447453867, 7297256490, 7150950653, 7008381443, 6869403642, 6733880894, 6601684956, 6472695034, 6346797176, 6223883738, 6103852890, 5986608183, 5872058142, 5760115913, 5650698925, 5543728597, 5439130065, 5336831928, 5236766023, 5138867215, 5043073206, 4949324356, 4857563524, 4767735915, 4679788943, 4593672106, 4509336863, 4426736525, 4345826159, 4266562487, 4188903802, 4112809883, 4038241925, 3965162461, 3893535298, 3823325459, 3754499118, 3687023552, 3620867086, 3555999047, 3492389716, 3430010292, 3368832846, 3308830287, 3249976324, 3192245438, 3135612842, 3080054460, 3025546894, 2972067398, 2919593852, 2868104743, 2817579135, 2767996653, 2719337460, 2671582240, 2624712174, 2578708931, 2533554644, 2489231895, 2445723704, 2403013511, 2361085163, 2319922899, 2279511340, 2239835478, 2200880658, 2162632574, 2125077255, 2088201055, 2051990643, 2016432995, 1981515384, 1947225370, 1913550794, 1880479770, 1848000675, 1816102144, 1784773061, 1754002553, 1723779984, 1694094947, 1664937261, 1636296959, 1608164290, 1580529708, 1553383868, 1526717621, 1500522011, 1474788265, 1449507795, 1424672187, 1400273203, 1376302771, 1352752985, 1329616097, 1306884518, 1284550812, 1262607690, 1241048010, 1219864774, 1199051119, 1178600322, 1158505791, 1138761061, 1119359799, 1100295791, 1081562947, 1063155294, 1045066975, 1027292247, 1009825477, 992661141, 975793818, 959218195, 942929058]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1325).prefactor = (449937424974203/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1325).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1325).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1325).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1325

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1325).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1325).criticalRate j.val*(generalMeanRows 1325).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1325).c*(generalMeanRows 1325).criticalPoint j.val)).2-
      (generalMeanRows 1325).J/2-(generalMeanRows 1325).error (generalMeanGrid j.val)+
      (generalMeanRows 1325).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1325).c)).2-
      (generalMeanRows 1325).J/2-(generalMeanRows 1325).error 4 := by
  have he : (generalMeanRows 1325).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1325) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1325)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1325

/-! Kernel-checked entropy margins for general spectral rectangle 1326. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1326
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8399187412, 8222016913, 8049854354, 7882472833, 7719661637, 7561224675, 7406979097, 7256754076, 7110389723, 6967736126, 6828652492, 6693006379, 6560673011, 6431534660, 6305480087, 6182404048, 6062206836, 5944793875, 5830075343, 5717965839, 5608384073, 5501252586, 5396497491, 5294048241, 5193837415, 5095800516, 4999875793, 4906004073, 4814128607, 4724194927, 4636150714, 4549945679, 4465531449, 4382861459, 4301890862, 4222576429, 4144876476, 4068750774, 3994160486, 3921068092, 3849437328, 3779233124, 3710421551, 3642969766, 3576845963, 3512019328, 3448459993, 3386138999, 3325028251, 3265100487, 3206329244, 3148688820, 3092154248, 3036701265, 2982306287, 2928946378, 2876599232, 2825243142, 2774856984, 2725420194, 2676912744, 2629315131, 2582608351, 2536773885, 2491793682, 2447650144, 2404326111, 2361804845, 2320070017, 2279105694, 2238896328, 2199426740, 2160682112, 2122647977, 2085310203, 2048654988, 2012668848, 1977338607, 1942651391, 1908594616, 1875155981, 1842323461, 1810085297, 1778429991, 1747346299, 1716823219, 1686849992, 1657416090, 1628511214, 1600125282, 1572248429, 1544871001, 1517983545, 1491576809, 1465641735, 1440169451, 1415151272, 1390578693, 1366443382, 1342737180, 1319452094, 1296580294, 1274114108, 1252046022, 1230368671, 1209074838, 1188157452, 1167609581, 1147424434, 1127595352, 1108115809, 1088979408, 1070179876, 1051711066, 1033566948, 1015741612, 998229262, 981024214, 964120896, 947513841, 931197689]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1326).prefactor = (231067462668131/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1326).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1326).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1326).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1326

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1326).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1326).criticalRate j.val*(generalMeanRows 1326).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1326).c*(generalMeanRows 1326).criticalPoint j.val)).2-
      (generalMeanRows 1326).J/2-(generalMeanRows 1326).error (generalMeanGrid j.val)+
      (generalMeanRows 1326).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1326).c)).2-
      (generalMeanRows 1326).J/2-(generalMeanRows 1326).error 4 := by
  have he : (generalMeanRows 1326).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1326) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1326)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1326

/-! Kernel-checked entropy margins for general spectral rectangle 1327. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1327
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8512274265, 8332718339, 8158237779, 7988602629, 7823599339, 7663029178, 7506706834, 7354459180, 7206124174, 7061549886, 6920593626, 6783121171, 6649006064, 6518128991, 6390377216, 6265644079, 6143828529, 6024834717, 5908571612, 5794952663, 5683895486, 5575321578, 5469156057, 5365327429, 5263767362, 5164410492, 5067194236, 4972058625, 4878946146, 4787801596, 4698571954, 4611206253, 4525655467, 4441872407, 4359811619, 4279429296, 4200683188, 4123532528, 4047937955, 3973861443, 3901266241, 3830116806, 3760378752, 3692018795, 3625004700, 3559305237, 3494890138, 3431730052, 3369796508, 3309061876, 3249499335, 3191082839, 3133787084, 3077587481, 3022460127, 2968381780, 2915329830, 2863282281, 2812217723, 2762115314, 2712954759, 2664716291, 2617380649, 2570929067, 2525343249, 2480605362, 2436698014, 2393604240, 2351307493, 2309791626, 2269040879, 2229039872, 2189773586, 2151227358, 2113386868, 2076238126, 2039767467, 2003961540, 1968807294, 1934291978, 1900403124, 1867128546, 1834456327, 1802374814, 1770872609, 1739938566, 1709561779, 1679731579, 1650437526, 1621669405, 1593417218, 1565671180, 1538421711, 1511659434, 1485375169, 1459559925, 1434204901, 1409301476, 1384841207, 1360815824, 1337217227, 1314037481, 1291268810, 1268903599, 1246934383, 1225353850, 1204154831, 1183330304, 1162873383, 1142777322, 1123035506, 1103641452, 1084588803, 1065871328, 1047482917, 1029417580, 1011669444, 994232747, 977101842, 960271189, 943735356]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1327).prefactor = (4683571206340049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1327).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1327).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1327).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1327

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1327).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1327).criticalRate j.val*(generalMeanRows 1327).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1327).c*(generalMeanRows 1327).criticalPoint j.val)).2-
      (generalMeanRows 1327).J/2-(generalMeanRows 1327).error (generalMeanGrid j.val)+
      (generalMeanRows 1327).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1327).c)).2-
      (generalMeanRows 1327).J/2-(generalMeanRows 1327).error 4 := by
  have he : (generalMeanRows 1327).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1327) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1327)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1327

/-! Kernel-checked entropy margins for general spectral rectangle 1328. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1328
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8191161206, 8019712326, 7853092796, 7691083540, 7533481140, 7380096326, 7230752634, 7085285227, 6943539844, 6805371875, 6670645523, 6539233064, 6411014186, 6285875386, 6163709435, 6044414893, 5927895673, 5814060640, 5702823256, 5594101249, 5487816318, 5383893858, 5282262717, 5182854963, 5085605683, 4990452784, 4897336822, 4806200842, 4716990225, 4629652553, 4544137479, 4460396614, 4378383415, 4298053083, 4219362472, 4142269999, 4066735565, 3992720476, 3920187376, 3849100180, 3779424008, 3711125135, 3644170930, 3578529808, 3514171184, 3451065425, 3389183810, 3328498489, 3268982447, 3210609469, 3153354106, 3097191644, 3042098072, 2988050059, 2935024925, 2883000613, 2831955669, 2781869219, 2732720946, 2684491072, 2637160334, 2590709971, 2545121704, 2500377719, 2456460651, 2413353570, 2371039965, 2329503733, 2288729162, 2248700920, 2209404045, 2170823929, 2132946310, 2095757263, 2059243186, 2023390790, 1988187095, 1953619416, 1919675355, 1886342794, 1853609887, 1821465052, 1789896963, 1758894544, 1728446960, 1698543615, 1669174138, 1640328386, 1611996431, 1584168556, 1556835253, 1529987212, 1503615322, 1477710659, 1452264488, 1427268253, 1402713576, 1378592253, 1354896244, 1331617678, 1308748840, 1286282173, 1264210273, 1242525884, 1221221897, 1200291343, 1179727392, 1159523351, 1139672659, 1120168883, 1101005717, 1082176980, 1063676610, 1045498665, 1027637315, 1010086848, 992841658, 975896249, 959245230, 942883315, 926805317]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1328).prefactor = (1089806461520589/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1328).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1328).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1328).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1328

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1328).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1328).criticalRate j.val*(generalMeanRows 1328).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1328).c*(generalMeanRows 1328).criticalPoint j.val)).2-
      (generalMeanRows 1328).J/2-(generalMeanRows 1328).error (generalMeanGrid j.val)+
      (generalMeanRows 1328).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1328).c)).2-
      (generalMeanRows 1328).J/2-(generalMeanRows 1328).error 4 := by
  have he : (generalMeanRows 1328).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1328) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1328)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1328

/-! Kernel-checked entropy margins for general spectral rectangle 1329. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1329
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![8318556774, 8142570010, 7971564380, 7805314299, 7643610265, 7486257302, 7333073588, 7183889249, 7038545279, 6896892583, 6758791130, 6624109187, 6492722640, 6364514376, 6239373737, 6117196019, 5997882024, 5881337652, 5767473531, 5656204684, 5547450219, 5441133053, 5337179658, 5235519824, 5136086448, 5038815339, 4943645035, 4850516636, 4759373654, 4670161872, 4582829208, 4497325601, 4413602895, 4331614733, 4251316467, 4172665060, 4095619011, 4020138269, 3946184166, 3873719345, 3802707699, 3733114312, 3664905400, 3598048262, 3532511229, 3468263620, 3405275696, 3343518619, 3282964419, 3223585950, 3165356861, 3108251561, 3052245192, 2997313594, 2943433285, 2890581430, 2838735817, 2787874836, 2737977453, 2689023194, 2640992122, 2593864816, 2547622357, 2502246308, 2457718700, 2414022014, 2371139165, 2329053491, 2287748738, 2247209046, 2207418937, 2168363304, 2130027397, 2092396815, 2055457495, 2019195698, 1983598005, 1948651304, 1914342782, 1880659916, 1847590466, 1815122465, 1783244213, 1751944269, 1721211445, 1691034796, 1661403617, 1632307434, 1603736001, 1575679289, 1548127486, 1521070986, 1494500389, 1468406492, 1442780285, 1417612946, 1392895837, 1368620499, 1344778649, 1321362172, 1298363121, 1275773710, 1253586313, 1231793458, 1210387823, 1189362234, 1168709662, 1148423218, 1128496149, 1108921839, 1089693802, 1070805678, 1052251237, 1034024367, 1016119078, 998529497, 981249867, 964274539, 947597977, 931214752, 915119538]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1329).prefactor = (4472135954999801/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1329).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1329).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1329).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1329

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1329).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1329).criticalRate j.val*(generalMeanRows 1329).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1329).c*(generalMeanRows 1329).criticalPoint j.val)).2-
      (generalMeanRows 1329).J/2-(generalMeanRows 1329).error (generalMeanGrid j.val)+
      (generalMeanRows 1329).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1329).c)).2-
      (generalMeanRows 1329).J/2-(generalMeanRows 1329).error 4 := by
  have he : (generalMeanRows 1329).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1329) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1329)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1329

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock18 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 18 i) := by
  fin_cases i
  · exact EntropyRow1260.numerical
  · exact EntropyRow1261.numerical
  · exact EntropyRow1262.numerical
  · exact EntropyRow1263.numerical
  · exact EntropyRow1264.numerical
  · exact EntropyRow1265.numerical
  · exact EntropyRow1266.numerical
  · exact EntropyRow1267.numerical
  · exact EntropyRow1268.numerical
  · exact EntropyRow1269.numerical
  · exact EntropyRow1270.numerical
  · exact EntropyRow1271.numerical
  · exact EntropyRow1272.numerical
  · exact EntropyRow1273.numerical
  · exact EntropyRow1274.numerical
  · exact EntropyRow1275.numerical
  · exact EntropyRow1276.numerical
  · exact EntropyRow1277.numerical
  · exact EntropyRow1278.numerical
  · exact EntropyRow1279.numerical
  · exact EntropyRow1280.numerical
  · exact EntropyRow1281.numerical
  · exact EntropyRow1282.numerical
  · exact EntropyRow1283.numerical
  · exact EntropyRow1284.numerical
  · exact EntropyRow1285.numerical
  · exact EntropyRow1286.numerical
  · exact EntropyRow1287.numerical
  · exact EntropyRow1288.numerical
  · exact EntropyRow1289.numerical
  · exact EntropyRow1290.numerical
  · exact EntropyRow1291.numerical
  · exact EntropyRow1292.numerical
  · exact EntropyRow1293.numerical
  · exact EntropyRow1294.numerical
  · exact EntropyRow1295.numerical
  · exact EntropyRow1296.numerical
  · exact EntropyRow1297.numerical
  · exact EntropyRow1298.numerical
  · exact EntropyRow1299.numerical
  · exact EntropyRow1300.numerical
  · exact EntropyRow1301.numerical
  · exact EntropyRow1302.numerical
  · exact EntropyRow1303.numerical
  · exact EntropyRow1304.numerical
  · exact EntropyRow1305.numerical
  · exact EntropyRow1306.numerical
  · exact EntropyRow1307.numerical
  · exact EntropyRow1308.numerical
  · exact EntropyRow1309.numerical
  · exact EntropyRow1310.numerical
  · exact EntropyRow1311.numerical
  · exact EntropyRow1312.numerical
  · exact EntropyRow1313.numerical
  · exact EntropyRow1314.numerical
  · exact EntropyRow1315.numerical
  · exact EntropyRow1316.numerical
  · exact EntropyRow1317.numerical
  · exact EntropyRow1318.numerical
  · exact EntropyRow1319.numerical
  · exact EntropyRow1320.numerical
  · exact EntropyRow1321.numerical
  · exact EntropyRow1322.numerical
  · exact EntropyRow1323.numerical
  · exact EntropyRow1324.numerical
  · exact EntropyRow1325.numerical
  · exact EntropyRow1326.numerical
  · exact EntropyRow1327.numerical
  · exact EntropyRow1328.numerical
  · exact EntropyRow1329.numerical
end SingularValueBounds.KL.Certificates
