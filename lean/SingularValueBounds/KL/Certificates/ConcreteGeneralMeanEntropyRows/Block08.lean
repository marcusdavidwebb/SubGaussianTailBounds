import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 560. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0560
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5316957247, 5149355833, 4989123736, 4835837389, 4689103351, 4548555667, 4413853528, 4284679161, 4160735948, 4041746724, 3927452243, 3817609792, 3711991935, 3610385369, 3512589882, 3418417406, 3327691149, 3240244802, 3155921808, 3074574696, 2996064464, 2920260016, 2847037635, 2776280504, 2707878258, 2641726574, 2577726788, 2515785536, 2455814431, 2397729755, 2341452173, 2286906469, 2234021301, 2182728969, 2132965201, 2084668954, 2037782224, 1992249874, 1948019470, 1905041124, 1863267357, 1822652959, 1783154865, 1744732038, 1707345354, 1670957504, 1635532891, 1601037539, 1567439008, 1534706311, 1502809840, 1471721291, 1441413595, 1411860860, 1383038305, 1354922205, 1327489839, 1300719436, 1274590131, 1249081918, 1224175606, 1199852783, 1176095774, 1152887607, 1130211979, 1108053225, 1086396283, 1065226671, 1044530457, 1024294235, 1004505096, 985150612, 966218806, 947698141, 929577490, 911846126, 894493697, 877510216, 860886040, 844611859, 828678676, 813077799, 797800827, 782839633, 768186360, 753833403, 739773401, 725999229, 712503985, 699280984, 686323745, 673625988, 661181623, 648984744, 637029618, 625310684, 613822543, 602559953, 591517821, 580691201, 570075286, 559665402, 549457006, 539445681, 529627127, 519997165, 510551723, 501286840, 492198660, 483283426, 474537479, 465957254, 457539278, 449280165, 441176615, 433225408, 425423407, 417767550, 410254849, 402882392, 395647332]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 560).prefactor = (574684715403257/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 560).cutoff/(generalMeanRows 560).c)).2 =
    (421595503595919/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 560).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 560).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 560).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 560

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 560).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 560).criticalRate j.val*(generalMeanRows 560).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 560).c*(generalMeanRows 560).criticalPoint j.val)).2-
      (generalMeanRows 560).J/2-(generalMeanRows 560).error (generalMeanGrid j.val)+
      (generalMeanRows 560).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 560).c)).2-
      (generalMeanRows 560).J/2-(generalMeanRows 560).error 4 := by
  have he : (generalMeanRows 560).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 560) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 560)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0560

/-! Kernel-checked entropy margins for general spectral rectangle 561. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0561
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5244887566, 5076998470, 4916514477, 4763010503, 4616091668, 4475390652, 4340565344, 4211296738, 4087287034, 3968257938, 3853949130, 3744116865, 3638532717, 3536982436, 3439264901, 3345191168, 3254583605, 3167275093, 3083108296, 3001934992, 2923615456, 2848017891, 2775017908, 2704498038, 2636347289, 2570460729, 2506739106, 2445088491, 2385419946, 2327649221, 2271696469, 2217485975, 2164945916, 2114008126, 2064607881, 2016683701, 1970177160, 1925032709, 1881197517, 1838621313, 1797256244, 1757056739, 1717979384, 1679982803, 1643027545, 1607075981, 1572092209, 1538041953, 1504892485, 1472612539, 1441172236, 1410543009, 1380697538, 1351609683, 1323254427, 1295607816, 1268646904, 1242349707, 1216695151, 1191663029, 1167233957, 1143389333, 1120111302, 1097382716, 1075187103, 1053508632, 1032332086, 1011642830, 991426785, 971670401, 952360634, 933484923, 915031167, 896987702, 879343287, 862087079, 845208618, 828697813, 812544918, 796740526, 781275550, 766141206, 751329007, 736830745, 722638484, 708744543, 695141490, 681822129, 668779495, 656006836, 643497614, 631245492, 619244323, 607488150, 595971191, 584687839, 573632650, 562800339, 552185774, 541783972, 531590089, 521599420, 511807389, 502209550, 492801577, 483579262, 474538513, 465675346, 456985884, 448466350, 440113071, 431922465, 423891044, 416015410, 408292252, 400718340, 393290528, 386005747, 378861004, 371853379, 364980024]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 561).prefactor = (4613228629972819/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 561).cutoff/(generalMeanRows 561).c)).2 =
    (413843526791601/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 561).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 561).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 561).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 561

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 561).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 561).criticalRate j.val*(generalMeanRows 561).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 561).c*(generalMeanRows 561).criticalPoint j.val)).2-
      (generalMeanRows 561).J/2-(generalMeanRows 561).error (generalMeanGrid j.val)+
      (generalMeanRows 561).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 561).c)).2-
      (generalMeanRows 561).J/2-(generalMeanRows 561).error 4 := by
  have he : (generalMeanRows 561).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 561) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 561)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0561

/-! Kernel-checked entropy margins for general spectral rectangle 562. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0562
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5264116453, 5095620418, 4934542672, 4780458358, 4632972760, 4491718678, 4356354069, 4226559951, 4102038513, 3982511414, 3867718252, 3757415175, 3651373627, 3549379201, 3451230602, 3356738696, 3265725644, 3178024107, 3093476521, 3011934424, 2933257844, 2857314732, 2783980440, 2713137237, 2644673868, 2578485135, 2514471519, 2452538822, 2392597844, 2334564068, 2278357383, 2223901817, 2171125287, 2119959374, 2070339104, 2022202748, 1975491639, 1930149992, 1886124740, 1843365384, 1801823848, 1761454342, 1722213238, 1684058951, 1646951828, 1610854041, 1575729494, 1541543724, 1508263821, 1475858342, 1444297232, 1413551760, 1383594442, 1354398981, 1325940206, 1298194015, 1271137319, 1244747996, 1219004836, 1193887503, 1169376485, 1145453062, 1122099258, 1099297812, 1077032144, 1055286316, 1034045008, 1013293487, 993017578, 973203640, 953838540, 934909632, 916404732, 898312097, 880620408, 863318751, 846396594, 829843775, 813650487, 797807257, 782304935, 767134683, 752287954, 737756488, 723532295, 709607644, 695975055, 682627287, 669557328, 656758385, 644223877, 631947428, 619922855, 608144161, 596605532, 585301325, 574226064, 563374434, 552741272, 542321567, 532110446, 522103179, 512295165, 502681932, 493259131, 484022532, 474968022, 466091595, 457389354, 448857505, 440492354, 432290303, 424247848, 416361573, 408628152, 401044342, 393606980, 386312984, 379159348, 372143141, 365261501]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 562).prefactor = (576936448928419/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 562).cutoff/(generalMeanRows 562).c)).2 =
    (41098229451057/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 562).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 562).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 562).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 562

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 562).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 562).criticalRate j.val*(generalMeanRows 562).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 562).c*(generalMeanRows 562).criticalPoint j.val)).2-
      (generalMeanRows 562).J/2-(generalMeanRows 562).error (generalMeanGrid j.val)+
      (generalMeanRows 562).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 562).c)).2-
      (generalMeanRows 562).J/2-(generalMeanRows 562).error 4 := by
  have he : (generalMeanRows 562).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 562) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 562)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0562

/-! Kernel-checked entropy margins for general spectral rectangle 563. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0563
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5193561456, 5024811455, 4863515547, 4709247305, 4561610529, 4420236607, 4284782158, 4154926923, 4030371874, 3910837512, 3796062324, 3685801399, 3579825165, 3477918241, 3379878399, 3285515609, 3194651170, 3107116916, 3022754486, 2941414650, 2862956699, 2787247872, 2714162835, 2643583195, 2575397057, 2509498608, 2445787734, 2384169663, 2324554637, 2266857605, 2210997938, 2156899160, 2104488706, 2053697687, 2004460676, 1956715507, 1910403089, 1865467224, 1821854453, 1779513890, 1738397090, 1698457902, 1659652353, 1621938521, 1585276427, 1549627932, 1514956633, 1481227776, 1448408164, 1416466080, 1385371206, 1355094551, 1325608385, 1296886170, 1268902504, 1241633061, 1215054536, 1189144599, 1163881838, 1139245721, 1115216552, 1091775427, 1068904196, 1046585432, 1024802389, 1003538975, 982779719, 962509743, 942714731, 923380910, 904495017, 886044280, 868016396, 850399509, 833182189, 816353415, 799902554, 783819348, 768093895, 752716633, 737678327, 722970056, 708583196, 694509412, 680740642, 667269088, 654087205, 641187689, 628563470, 616207700, 604113746, 592275179, 580685769, 569339476, 558230442, 547352984, 536701590, 526270908, 516055743, 506051052, 496251935, 486653633, 477251520, 468041103, 459018011, 450177996, 441516923, 433030774, 424715637, 416567704, 408583271, 400758729, 393090565, 385575358, 378209775, 370990567, 363914570, 356978698, 350179946, 343515381, 336982144]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 563).prefactor = (2315717265347287/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 563).cutoff/(generalMeanRows 563).c)).2 =
    (80657989777483/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 563).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 563).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 563).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 563

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 563).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 563).criticalRate j.val*(generalMeanRows 563).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 563).c*(generalMeanRows 563).criticalPoint j.val)).2-
      (generalMeanRows 563).J/2-(generalMeanRows 563).error (generalMeanGrid j.val)+
      (generalMeanRows 563).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 563).c)).2-
      (generalMeanRows 563).J/2-(generalMeanRows 563).error 4 := by
  have he : (generalMeanRows 563).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 563) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 563)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0563

/-! Kernel-checked entropy margins for general spectral rectangle 564. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0564
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5060300749, 4891104859, 4729408284, 4574784747, 4426838049, 4285199446, 4149525305, 4019495007, 3894809067, 3775187441, 3660367994, 3550105125, 3444168511, 3342341970, 3244422422, 3150218949, 3059551928, 2972252244, 2888160559, 2807126654, 2729008809, 2653673246, 2580993606, 2510850466, 2443130900, 2377728063, 2314540815, 2253473362, 2194434934, 2137339475, 2082105360, 2028655134, 1976915262, 1926815901, 1878290685, 1831276526, 1785713425, 1741544299, 1698714814, 1657173235, 1616870281, 1577758989, 1539794587, 1502934378, 1467137628, 1432365456, 1398580745, 1365748039, 1333833463, 1302804639, 1272630607, 1243281755, 1214729746, 1186947458, 1159908922, 1133589261, 1107964639, 1083012209, 1058710063, 1035037189, 1011973424, 989499416, 967596583, 946247080, 925433759, 905140140, 885350380, 866049241, 847222062, 828854738, 810933687, 793445831, 776378575, 759719780, 743457746, 727581194, 712079246, 696941405, 682157544, 667717886, 653612991, 639833741, 626371327, 613217234, 600363234, 587801367, 575523938, 563523498, 551792841, 540324991, 529113194, 518150906, 507431791, 496949707, 486698703, 476673008, 466867025, 457275328, 447892652, 438713886, 429734071, 420948393, 412352176, 403940880, 395710093, 387655530, 379773024, 372058527, 364508102, 357117921, 349884261, 342803500, 335872114, 329086674, 322443841, 315940366, 309573086, 303338919, 297234865, 291258001, 285405478]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 564).prefactor = (1159058056089423/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 564).cutoff/(generalMeanRows 564).c)).2 =
    (93355104763/244140625000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 564).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 564).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 564).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 564

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 564).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 564).criticalRate j.val*(generalMeanRows 564).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 564).c*(generalMeanRows 564).criticalPoint j.val)).2-
      (generalMeanRows 564).J/2-(generalMeanRows 564).error (generalMeanGrid j.val)+
      (generalMeanRows 564).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 564).c)).2-
      (generalMeanRows 564).J/2-(generalMeanRows 564).error 4 := by
  have he : (generalMeanRows 564).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 564) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 564)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0564

/-! Kernel-checked entropy margins for general spectral rectangle 565. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0565
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5126056862, 4957063571, 4795547328, 4641081793, 4493270779, 4351745617, 4216162808, 4086201922, 3961563708, 3841968399, 3727154176, 3616875788, 3510903288, 3409020898, 3311025966, 3216728018, 3125947894, 3038516952, 2954276342, 2873076339, 2794775727, 2719241235, 2646347013, 2575974153, 2508010241, 2442348945, 2378889634, 2317537023, 2258200843, 2200795538, 2145239977, 2091457190, 2039374123, 1988921405, 1940033136, 1892646684, 1846702500, 1802143938, 1758917097, 1716970663, 1676255765, 1636725843, 1598336520, 1561045480, 1524812363, 1489598652, 1455367584, 1422084047, 1389714501, 1358226893, 1327590579, 1297776251, 1268755872, 1240502607, 1212990765, 1186195738, 1160093953, 1134662813, 1109880656, 1085726704, 1062181022, 1039224477, 1016838699, 995006045, 973709565, 952932968, 932660592, 912877373, 893568820, 874720987, 856320448, 838354274, 820810011, 803675656, 786939640, 770590809, 754618402, 739012039, 723761699, 708857711, 694290731, 680051736, 666132005, 652523110, 639216901, 626205497, 613481271, 601036844, 588865075, 576959048, 565312065, 553917637, 542769476, 531861489, 521187766, 510742579, 500520369, 490515743, 480723469, 471138466, 461755801, 452570685, 443578464, 434774618, 426154754, 417714600, 409450004, 401356930, 393431450, 385669745, 378068097, 370622888, 363330598, 356187799, 349191152, 342337407, 335623396, 329046035, 322602318, 316289315, 310104169]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 565).prefactor = (2316916912202153/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 565).cutoff/(generalMeanRows 565).c)).2 =
    (392803255049937/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 565).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 565).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 565).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 565

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 565).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 565).criticalRate j.val*(generalMeanRows 565).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 565).c*(generalMeanRows 565).criticalPoint j.val)).2-
      (generalMeanRows 565).J/2-(generalMeanRows 565).error (generalMeanGrid j.val)+
      (generalMeanRows 565).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 565).c)).2-
      (generalMeanRows 565).J/2-(generalMeanRows 565).error 4 := by
  have he : (generalMeanRows 565).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 565) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 565)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0565

/-! Kernel-checked entropy margins for general spectral rectangle 566. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0566
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5143910203, 4974328332, 4812249550, 4657246034, 4508920214, 4366902140, 4230847116, 4100433594, 3975361282, 3855349439, 3740135334, 3629472862, 3523131275, 3420894043, 3322557808, 3227931434, 3136835135, 3049099683, 2964565674, 2883082863, 2804509541, 2728711973, 2655563871, 2584945912, 2516745291, 2450855306, 2387174975, 2325608681, 2266065842, 2208460602, 2152711549, 2098741444, 2046476978, 1995848541, 1946790001, 1899238509, 1853134307, 1808420554, 1765043160, 1722950632, 1682093930, 1642426331, 1603903303, 1566482384, 1530123071, 1494786717, 1460436426, 1427036967, 1394554683, 1362957408, 1332214392, 1302296225, 1273174772, 1244823105, 1217215443, 1190327093, 1164134398, 1138614686, 1113746216, 1089508139, 1065880450, 1042843951, 1020380206, 998471512, 977100860, 956251901, 935908919, 916056798, 896680996, 877767518, 859302893, 841274145, 823668778, 806474746, 789680441, 773274669, 757246633, 741585915, 726282460, 711326563, 696708849, 682420261, 668452050, 654795757, 641443205, 628386483, 615617940, 603130172, 590916010, 578968516, 567280968, 555846854, 544659866, 533713888, 523002991, 512521424, 502263612, 492224141, 482397762, 472779375, 463364032, 454146925, 445123386, 436288878, 427638991, 419169441, 410876062, 402754800, 394801717, 387012979, 379384855, 371913716, 364596028, 357428351, 350407336, 343529720, 336792326, 330192057, 323725897, 317390906, 311184219]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 566).prefactor = (116249320537707/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 566).cutoff/(generalMeanRows 566).c)).2 =
    (392803255049937/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 566).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 566).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 566).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 566

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 566).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 566).criticalRate j.val*(generalMeanRows 566).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 566).c*(generalMeanRows 566).criticalPoint j.val)).2-
      (generalMeanRows 566).J/2-(generalMeanRows 566).error (generalMeanGrid j.val)+
      (generalMeanRows 566).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 566).c)).2-
      (generalMeanRows 566).J/2-(generalMeanRows 566).error 4 := by
  have he : (generalMeanRows 566).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 566) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 566)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0566

/-! Kernel-checked entropy margins for general spectral rectangle 567. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0567
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5078072070, 4908281980, 4746017541, 4590850980, 4442384706, 4300248681, 4164098065, 4033611113, 3908487287, 3788445560, 3673222877, 3562572775, 3456264122, 3354079974, 3255816542, 3161282235, 3070296800, 2982690527, 2898303520, 2816985030, 2738592843, 2662992708, 2590057824, 2519668347, 2451710956, 2386078430, 2322669274, 2261387358, 2202141593, 2144845619, 2089417527, 2035779589, 1983858011, 1933582705, 1884887073, 1837707804, 1791984690, 1747660446, 1704680548, 1662993079, 1622548585, 1583299937, 1545202207, 1508212549, 1472290083, 1437395795, 1403492435, 1370544423, 1338517767, 1307379972, 1277099972, 1247648048, 1218995767, 1191115911, 1163982418, 1137570324, 1111855711, 1086815650, 1062428158, 1038672147, 1015527384, 992974449, 970994696, 949570215, 928683799, 908318911, 888459651, 869090728, 850197430, 831765601, 813781613, 796232342, 779105147, 762387847, 746068703, 730136394, 714580004, 699389000, 684553220, 670062851, 655908421, 642080780, 628571086, 615370798, 602471656, 589865673, 577545126, 565502542, 553730688, 542222564, 530971392, 519970606, 509213846, 498694950, 488407945, 478347040, 468506620, 458881238, 449465611, 440254610, 431243259, 422426726, 413800320, 405359484, 397099792, 389016941, 381106753, 373365163, 365788222, 358372087, 351113023, 344007395, 337051667, 330242397, 323576235, 317049920, 310660279, 304404218, 298278727, 292280873, 286407796]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 567).prefactor = (930502851087753/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 567).cutoff/(generalMeanRows 567).c)).2 =
    (93355104763/244140625000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 567).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 567).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 567).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 567

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 567).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 567).criticalRate j.val*(generalMeanRows 567).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 567).c*(generalMeanRows 567).criticalPoint j.val)).2-
      (generalMeanRows 567).J/2-(generalMeanRows 567).error (generalMeanGrid j.val)+
      (generalMeanRows 567).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 567).c)).2-
      (generalMeanRows 567).J/2-(generalMeanRows 567).error 4 := by
  have he : (generalMeanRows 567).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 567) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 567)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0567

/-! Kernel-checked entropy margins for general spectral rectangle 568. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0568
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5012003850, 4842057621, 4679672355, 4524418586, 4375897121, 4233736404, 4097590153, 3967135255, 3842069870, 3722111729, 3606996594, 3496476873, 3390320353, 3288309062, 3190238220, 3095915292, 3005159120, 2917799125, 2833674576, 2752633926, 2674534191, 2599240385, 2526624993, 2456567494, 2388953907, 2323676383, 2260632818, 2199726498, 2140865771, 2083963737, 2028937964, 1975710220, 1924206230, 1874355439, 1826090799, 1779348567, 1734068117, 1690191764, 1647664597, 1606434327, 1566451139, 1527667560, 1490038329, 1453520278, 1418072220, 1383654842, 1350230608, 1317763665, 1286219753, 1255566124, 1225771466, 1196805825, 1168640539, 1141248174, 1114602458, 1088678226, 1063451367, 1038898767, 1014998263, 991728598, 969069375, 947001017, 925504728, 904562454, 884156851, 864271248, 844889620, 825996556, 807577230, 789617374, 772103257, 755021655, 738359831, 722105516, 706246882, 690772530, 675671463, 660933078, 646547140, 632503774, 618793444, 605406942, 592335372, 579570138, 567102935, 554925730, 543030757, 531410504, 520057700, 508965313, 498126531, 487534761, 477183617, 467066911, 457178650, 447513022, 438064395, 428827306, 419796459, 410966713, 402333082, 393890726, 385634948, 377561185, 369665008, 361942114, 354388322, 346999570, 339771910, 332701504, 325784621, 319017633, 312397009, 305919316, 299581216, 293379456, 287310873, 281372388, 275561003, 269873797, 264307928]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 568).prefactor = (933770693510063/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 568).cutoff/(generalMeanRows 568).c)).2 =
    (18743183834761/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 568).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 568).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 568).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 568

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 568).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 568).criticalRate j.val*(generalMeanRows 568).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 568).c*(generalMeanRows 568).criticalPoint j.val)).2-
      (generalMeanRows 568).J/2-(generalMeanRows 568).error (generalMeanGrid j.val)+
      (generalMeanRows 568).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 568).c)).2-
      (generalMeanRows 568).J/2-(generalMeanRows 568).error 4 := by
  have he : (generalMeanRows 568).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 568) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 568)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0568

/-! Kernel-checked entropy margins for general spectral rectangle 569. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0569
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5174236168, 5006097782, 4845400056, 4691716355, 4544650325, 4403833249, 4268921690, 4139595375, 4015555299, 3896522019, 3782234114, 3672446786, 3566930605, 3465470352, 3367863980, 3273921656, 3183464892, 3096325748, 3012346096, 2931376952, 2853277858, 2777916309, 2705167235, 2634912509, 2567040503, 2501445674, 2438028176, 2376693510, 2317352185, 2259919418, 2204314845, 2150462254, 2098289338, 2047727465, 1998711461, 1951179408, 1905072459, 1860334657, 1816912776, 1774756163, 1733816595, 1694048144, 1655407050, 1617851602, 1581342025, 1545840379, 1511310457, 1477717691, 1445029070, 1413213054, 1382239499, 1352079583, 1322705737, 1294091585, 1266211877, 1239042435, 1212560100, 1186742678, 1161568896, 1137018352, 1113071474, 1089709482, 1066914344, 1044668747, 1022956055, 1001760283, 981066062, 960858613, 941123717, 921847692, 903017364, 884620048, 866643522, 849076011, 831906161, 815123025, 798716043, 782675023, 766990130, 751651865, 736651057, 721978840, 707626650, 693586204, 679849494, 666408771, 653256540, 640385543, 627788754, 615459369, 603390796, 591576646, 580010727, 568687037, 557599751, 546743222, 536111970, 525700673, 515504167, 505517438, 495735613, 486153960, 476767880, 467572902, 458564680, 449738987, 441091713, 432618857, 424316529, 416180941, 408208404, 400395330, 392738222, 385233675, 377878370, 370669076, 363602642, 356675996, 349886145, 343230169, 336705222]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 569).prefactor = (2314516749574091/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 569).cutoff/(generalMeanRows 569).c)).2 =
    (81230236233689/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 569).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 569).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 569).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 569

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 569).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 569).criticalRate j.val*(generalMeanRows 569).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 569).c*(generalMeanRows 569).criticalPoint j.val)).2-
      (generalMeanRows 569).J/2-(generalMeanRows 569).error (generalMeanGrid j.val)+
      (generalMeanRows 569).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 569).c)).2-
      (generalMeanRows 569).J/2-(generalMeanRows 569).error 4 := by
  have he : (generalMeanRows 569).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 569) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 569)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0569

/-! Kernel-checked entropy margins for general spectral rectangle 570. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0570
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5191963043, 5023248616, 4862000342, 4707790122, 4560220245, 4418920732, 4283546967, 4153777582, 4029312546, 3909871460, 3795192005, 3685028547, 3579150869, 3477343014, 3379402244, 3285138074, 3194371407, 3106933725, 3022666359, 2941419816, 2863053155, 2787433419, 2714435107, 2643939689, 2575835155, 2510015598, 2446380833, 2384836035, 2325291407, 2267661877, 2211866803, 2157829713, 2105478054, 2054742956, 2005559024, 1957864127, 1911599215, 1866708142, 1823137499, 1780836458, 1739756631, 1699851934, 1661078456, 1623394343, 1586759685, 1551136411, 1516488189, 1482780335, 1449979723, 1418054706, 1386975036, 1356711792, 1327237312, 1298525128, 1270549904, 1243287380, 1216714317, 1190808445, 1165548418, 1140913764, 1116884844, 1093442814, 1070569581, 1048247770, 1026460691, 1005192302, 984427183, 964150504, 944347997, 925005932, 906111091, 887650746, 869612633, 851984936, 834756263, 817915628, 801452435, 785356459, 769617829, 754227016, 739174815, 724452332, 710050971, 695962423, 682178650, 668691880, 655494589, 642579496, 629939551, 617567926, 605458006, 593603381, 581997838, 570635352, 559510082, 548616359, 537948683, 527501717, 517270278, 507249335, 497433997, 487819518, 478401281, 469174801, 460135717, 451279788, 442602888, 434101005, 425770233, 417606772, 409606922, 401767080, 394083739, 386553481, 379172977, 371938984, 364848340, 357897964, 351084851, 344406072, 337858770]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 570).prefactor = (11612231289067/2500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 570).cutoff/(generalMeanRows 570).c)).2 =
    (81230236233689/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 570).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 570).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 570).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 570

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 570).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 570).criticalRate j.val*(generalMeanRows 570).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 570).c*(generalMeanRows 570).criticalPoint j.val)).2-
      (generalMeanRows 570).J/2-(generalMeanRows 570).error (generalMeanGrid j.val)+
      (generalMeanRows 570).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 570).c)).2-
      (generalMeanRows 570).J/2-(generalMeanRows 570).error 4 := by
  have he : (generalMeanRows 570).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 570) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 570)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0570

/-! Kernel-checked entropy margins for general spectral rectangle 571. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0571
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5124391998, 4955425021, 4793947678, 4639531940, 4491780090, 4350322074, 4214813143, 4084931738, 3960377589, 3840870014, 3726146370, 3615960667, 3510082298, 3408294893, 3310395275, 3216192503, 3125507002, 3038169767, 2954021628, 2872912581, 2794701169, 2719253910, 2646444778, 2576154714, 2508271179, 2442687738, 2379303678, 2318023650, 2258757340, 2201419159, 2145927956, 2092206757, 2040182510, 1989785860, 1940950927, 1893615110, 1847718895, 1803205678, 1760021605, 1718115413, 1677438286, 1637943722, 1599587402, 1562327075, 1526122442, 1490935054, 1456728212, 1423466872, 1391117560, 1359648291, 1329028486, 1299228907, 1270221580, 1241979736, 1214477749, 1187691075, 1161596201, 1136170596, 1111392654, 1087241657, 1063697727, 1040741789, 1018355527, 996521351, 975222363, 954442321, 934165613, 914377223, 895062705, 876208158, 857800198, 839825938, 822272963, 805129310, 788383447, 772024255, 756041008, 740423359, 725161319, 710245247, 695665829, 681414070, 667481276, 653859044, 640539250, 627514034, 614775795, 602317174, 590131050, 578210527, 566548925, 555139774, 543976803, 533053933, 522365272, 511905104, 501667886, 491648236, 481840935, 472240913, 462843251, 453643166, 444636017, 435817292, 427182606, 418727697, 410448419, 402340744, 394400750, 386624624, 379008655, 371549230, 364242834, 357086042, 350075522, 343208026, 336480392, 329889536, 323432457, 317106227, 310907994]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 571).prefactor = (4647432540436399/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 571).cutoff/(generalMeanRows 571).c)).2 =
    (395656324032343/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 571).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 571).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 571).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 571

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 571).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 571).criticalRate j.val*(generalMeanRows 571).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 571).c*(generalMeanRows 571).criticalPoint j.val)).2-
      (generalMeanRows 571).J/2-(generalMeanRows 571).error (generalMeanGrid j.val)+
      (generalMeanRows 571).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 571).c)).2-
      (generalMeanRows 571).J/2-(generalMeanRows 571).error 4 := by
  have he : (generalMeanRows 571).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 571) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 571)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0571

/-! Kernel-checked entropy margins for general spectral rectangle 572. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0572
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5056579096, 4887430777, 4725807339, 4571279117, 4423446844, 4281938999, 4146409438, 4016535272, 3892014971, 3772566647, 3657926508, 3547847464, 3442097859, 3340460318, 3242730699, 3148717139, 3058239178, 2971126958, 2887220496, 2806369001, 2728430260, 2653270069, 2580761701, 2510785424, 2443228053, 2377982529, 2314947537, 2254027152, 2195130497, 2138171447, 2083068333, 2029743678, 1978123949, 1928139323, 1879723473, 1832813363, 1787349061, 1743273560, 1700532615, 1659074588, 1618850301, 1579812902, 1541917734, 1505122222, 1469385752, 1434669574, 1400936694, 1368151790, 1336281115, 1305292423, 1275154884, 1245839015, 1217316610, 1189560675, 1162545366, 1136245931, 1110638658, 1085700819, 1061410626, 1037747180, 1014690434, 992221145, 970320840, 948971777, 928156912, 907859864, 888064885, 868756831, 849921135, 831543774, 813611255, 796110582, 779029237, 762355157, 746076719, 730182712, 714662326, 699505132, 684701065, 670240408, 656113780, 642312119, 628826668, 615648966, 602770831, 590184353, 577881879, 565856005, 554099564, 542605621, 531367457, 520378566, 509632644, 499123582, 488845457, 478792530, 468959231, 459340159, 449930073, 440723887, 431716664, 422903609, 414280067, 405841517, 397583563, 389501937, 381592487, 373851181, 366274094, 358857412, 351597422, 344490514, 337533173, 330721981, 324053608, 317524812, 311132437, 304873409, 298744735, 292743495, 286866848]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 572).prefactor = (4663485810878553/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 572).cutoff/(generalMeanRows 572).c)).2 =
    (77616106044777/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 572).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 572).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 572).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 572

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 572).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 572).criticalRate j.val*(generalMeanRows 572).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 572).c*(generalMeanRows 572).criticalPoint j.val)).2-
      (generalMeanRows 572).J/2-(generalMeanRows 572).error (generalMeanGrid j.val)+
      (generalMeanRows 572).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 572).c)).2-
      (generalMeanRows 572).J/2-(generalMeanRows 572).error 4 := by
  have he : (generalMeanRows 572).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 572) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 572)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0572

/-! Kernel-checked entropy margins for general spectral rectangle 573. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0573
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5122462851, 4953535398, 4792109513, 4637755505, 4490074152, 4348694044, 4213269205, 4083476970, 3959016077, 3839604947, 3724980139, 3614894942, 3509118110, 3407432701, 3309635031, 3215533710, 3124948768, 3037710851, 2953660487, 2872647406, 2794529924, 2719174367, 2646454542, 2576251254, 2508451850, 2442949805, 2379644336, 2318440041, 2259246569, 2201978308, 2146554100, 2092896971, 2040933884, 1990595504, 1941815983, 1894532755, 1848686349, 1804220212, 1761080540, 1719216127, 1678578220, 1639120376, 1600798345, 1563569942, 1527394936, 1492234947, 1458053346, 1424815161, 1392486988, 1361036912, 1330434425, 1300650357, 1271656804, 1243427065, 1215935581, 1189157874, 1163070497, 1137650979, 1112877779, 1088730240, 1065188543, 1042233668, 1019847359, 998012078, 976710982, 955927880, 935647209, 915854003, 896533862, 877672930, 859257868, 841275830, 823714443, 806561782, 789806354, 773437076, 757443257, 741814583, 726541099, 711613193, 697021581, 682757298, 668811676, 655176339, 641843187, 628804385, 616052353, 603579756, 591379492, 579444685, 567768675, 556345009, 545167432, 534229884, 523526486, 513051537, 502799507, 492765030, 482942897, 473328050, 463915581, 454700719, 445678830, 436845413, 428196091, 419726611, 411432835, 403310740, 395356412, 387566045, 379935933, 372462469, 365142141, 357971532, 350947311, 344066236, 337325148, 330720967, 324250693, 317911403, 311700246]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 573).prefactor = (2330402932458367/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 573).cutoff/(generalMeanRows 573).c)).2 =
    (12453673634793/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 573).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 573).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 573).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 573

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 573).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 573).criticalRate j.val*(generalMeanRows 573).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 573).c*(generalMeanRows 573).criticalPoint j.val)).2-
      (generalMeanRows 573).J/2-(generalMeanRows 573).error (generalMeanGrid j.val)+
      (generalMeanRows 573).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 573).c)).2-
      (generalMeanRows 573).J/2-(generalMeanRows 573).error 4 := by
  have he : (generalMeanRows 573).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 573) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 573)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0573

/-! Kernel-checked entropy margins for general spectral rectangle 574. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0574
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5054326739, 4885222016, 4723653978, 4569191307, 4421433243, 4280006915, 4144564958, 4014783388, 3890359685, 3771011074, 3656472966, 3546497560, 3440852561, 3339320029, 3241695318, 3147786119, 3057411580, 2970401499, 2886595591, 2805842804, 2728000700, 2652934883, 2580518463, 2510631573, 2443160915, 2377999343, 2315045473, 2254203326, 2195381992, 2138495323, 2083461643, 2030203477, 1978647307, 1928723332, 1880365255, 1833510077, 1788097910, 1744071797, 1701377545, 1659963574, 1619780766, 1580782332, 1542923682, 1506162307, 1470457661, 1435771065, 1402065595, 1369305998, 1337458600, 1306491224, 1276373110, 1247074846, 1218568295, 1190826529, 1163823773, 1137535341, 1111937584, 1087007838, 1062724378, 1039066366, 1016013813, 993547534, 971649113, 950300863, 929485791, 909187569, 889390500, 870079487, 851240009, 832858091, 814920282, 797413627, 780325651, 763644330, 747358077, 731455720, 715926482, 700759968, 685946146, 671475330, 657338169, 643525628, 630028978, 616839784, 603949890, 591351409, 579036710, 566998413, 555229370, 543722666, 532471602, 521469688, 510710638, 500188360, 489896947, 479830671, 469983979, 460351483, 450927954, 441708317, 432687646, 423861158, 415224207, 406772281, 398500993, 390406083, 382483409, 374728942, 367138767, 359709074, 352436159, 345316415, 338346333, 331522499, 324841588, 318300362, 311895670, 305624439, 299483680, 293470476, 287581989]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 574).prefactor = (2338386866580789/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 574).cutoff/(generalMeanRows 574).c)).2 =
    (195470881252459/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 574).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 574).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 574).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 574

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 574).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 574).criticalRate j.val*(generalMeanRows 574).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 574).c*(generalMeanRows 574).criticalPoint j.val)).2-
      (generalMeanRows 574).J/2-(generalMeanRows 574).error (generalMeanGrid j.val)+
      (generalMeanRows 574).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 574).c)).2-
      (generalMeanRows 574).J/2-(generalMeanRows 574).error 4 := by
  have he : (generalMeanRows 574).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 574) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 574)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0574

/-! Kernel-checked entropy margins for general spectral rectangle 575. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0575
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5074045650, 4904313055, 4742131334, 4587069337, 4438726418, 4296729774, 4160732062, 4030409283, 3905458861, 3785597935, 3670561803, 3560102522, 3453987634, 3351999014, 3253931816, 3159593512, 3068803019, 2981389895, 2897193601, 2816062826, 2737854868, 2662435057, 2589676228, 2519458238, 2451667509, 2386196612, 2322943884, 2261813065, 2202712969, 2145557169, 2090263717, 2036754866, 1984956831, 1934799547, 1886216458, 1839144310, 1793522964, 1749295216, 1706406635, 1664805402, 1624442172, 1585269928, 1547243863, 1510321250, 1474461339, 1439625243, 1405775843, 1372877692, 1340896929, 1309801195, 1279559554, 1250142421, 1221521494, 1193669683, 1166561057, 1140170779, 1114475052, 1089451073, 1065076975, 1041331791, 1018195402, 995648498, 973672545, 952249737, 931362973, 910995814, 891132459, 871757712, 852856952, 834416112, 816421651, 798860526, 781720178, 764988502, 748653834, 732704926, 717130929, 701921379, 687066175, 672555568, 658380144, 644530808, 630998776, 617775555, 604852937, 592222982, 579878012, 567810598, 556013548, 544479902, 533202919, 522176070, 511393029, 500847666, 490534039, 480446386, 470579121, 460926822, 451484232, 442246246, 433207910, 424364413, 415711083, 407243384, 398956905, 390847363, 382910593, 375142547, 367539287, 360096985, 352811918, 345680461, 338699088, 331864369, 325172961, 318621613, 312207158, 305926510, 299776666, 293754696, 287857750]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 575).prefactor = (4679594532903853/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 575).cutoff/(generalMeanRows 575).c)).2 =
    (77616106044777/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 575).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 575).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 575).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 575

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 575).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 575).criticalRate j.val*(generalMeanRows 575).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 575).c*(generalMeanRows 575).criticalPoint j.val)).2-
      (generalMeanRows 575).J/2-(generalMeanRows 575).error (generalMeanGrid j.val)+
      (generalMeanRows 575).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 575).c)).2-
      (generalMeanRows 575).J/2-(generalMeanRows 575).error 4 := by
  have he : (generalMeanRows 575).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 575) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 575)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0575

/-! Kernel-checked entropy margins for general spectral rectangle 576. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0576
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5007331356, 4837451229, 4675157018, 4520015899, 4371625643, 4229611943, 4093626033, 3963342556, 3838457649, 3718687220, 3603765396, 3493443113, 3387486845, 3285677443, 3187809081, 3093688295, 3003133100, 2915972194, 2832044208, 2751197037, 2673287216, 2598179341, 2525745543, 2455864998, 2388423477, 2323312923, 2260431069, 2199681073, 2140971188, 2084214449, 2029328385, 1976234753, 1924859282, 1875131443, 1826984233, 1780353967, 1735180089, 1691404995, 1648973868, 1607834519, 1567937241, 1529234676, 1491681681, 1455235211, 1419854207, 1385499485, 1352133641, 1319720952, 1288227293, 1257620050, 1227868041, 1198941447, 1170811738, 1143451607, 1116834914, 1090936619, 1065732734, 1041200269, 1017317181, 994062331, 971415436, 949357031, 927868429, 906931683, 886529552, 866645466, 847263499, 828368332, 809945232, 791980021, 774459052, 757369185, 740697764, 724432596, 708561929, 693074433, 677959184, 663205643, 648803640, 634743361, 621015329, 607610393, 594519711, 581734741, 569247224, 557049177, 545132880, 533490862, 522115897, 511000989, 500139367, 489524473, 479149955, 469009658, 459097619, 449408057, 439935367, 430674114, 421619025, 412764984, 404107029, 395640339, 387360238, 379262182, 371341760, 363594686, 356016794, 348604039, 341352485, 334258308, 327317789, 320527310, 313883353, 307382494, 301021404, 294796838, 288705643, 282744745, 276911153, 271201953, 265614308]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 576).prefactor = (2347879449027221/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 576).cutoff/(generalMeanRows 576).c)).2 =
    (190280848904929/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 576).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 576).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 576).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 576

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 576).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 576).criticalRate j.val*(generalMeanRows 576).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 576).c*(generalMeanRows 576).criticalPoint j.val)).2-
      (generalMeanRows 576).J/2-(generalMeanRows 576).error (generalMeanGrid j.val)+
      (generalMeanRows 576).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 576).c)).2-
      (generalMeanRows 576).J/2-(generalMeanRows 576).error 4 := by
  have he : (generalMeanRows 576).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 576) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 576)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0576

/-! Kernel-checked entropy margins for general spectral rectangle 577. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0577
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5076190833, 4906422839, 4744193435, 4589073144, 4440662837, 4298591078, 4162511765, 4032102012, 3907060253, 3787104531, 3671970958, 3561412318, 3455196808, 3353106884, 3254938217, 3160498741, 3069607778, 2982095243, 2897800912, 2816573747, 2738271282, 2662759050, 2589910060, 2519604314, 2451728354, 2386174851, 2322842220, 2261634260, 2202459828, 2145232526, 2089870421, 2036295771, 1984434782, 1934217374, 1885576965, 1838450269, 1792777110, 1748500239, 1705565176, 1663920051, 1623515459, 1584304327, 1546241783, 1509285039, 1473393277, 1438527546, 1404650657, 1371727096, 1339722935, 1308605745, 1278344522, 1248909615, 1220272652, 1192406481, 1165285101, 1138883612, 1113178155, 1088145863, 1063764810, 1040013968, 1016873159, 994323018, 972344954, 950921108, 930034326, 909668119, 889806635, 870434630, 851537439, 833100949, 815111574, 797556231, 780422320, 763697697, 747370659, 731429923, 715864606, 700664209, 685818599, 671317997, 657152958, 643314360, 629793390, 616581530, 603670546, 591052476, 578719617, 566664520, 554879971, 543358991, 532094818, 521080907, 510310915, 499778694, 489478288, 479403920, 469549988, 459911061, 450481864, 441257285, 432232355, 423402256, 414762304, 406307952, 398034784, 389938505, 382014944, 374260044, 366669863, 359240565, 351968420, 344849798, 337881170, 331059097, 324380235, 317841327, 311439202, 305170772, 299033030, 293023043, 287137958]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 577).prefactor = (4666168028488871/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 577).cutoff/(generalMeanRows 577).c)).2 =
    (385227461241481/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 577).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 577).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 577).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 577

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 577).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 577).criticalRate j.val*(generalMeanRows 577).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 577).c*(generalMeanRows 577).criticalPoint j.val)).2-
      (generalMeanRows 577).J/2-(generalMeanRows 577).error (generalMeanGrid j.val)+
      (generalMeanRows 577).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 577).c)).2-
      (generalMeanRows 577).J/2-(generalMeanRows 577).error 4 := by
  have he : (generalMeanRows 577).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 577) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 577)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0577

/-! Kernel-checked entropy margins for general spectral rectangle 578. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0578
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5009796901, 4839877105, 4677531075, 4522327652, 4373866112, 4231773511, 4095702313, 3965328270, 3840348519, 3720479868, 3605457252, 3495032332, 3388972227, 3287058368, 3189085443, 3094860443, 3004201788, 2916938528, 2832909607, 2751963190, 2673956045, 2598752971, 2526226268, 2456255258, 2388725829, 2323530023, 2260565647, 2199735920, 2140949136, 2084118358, 2029161129, 1975999208, 1924558317, 1874767910, 1826560958, 1779873743, 1734645671, 1690819094, 1648339144, 1607153580, 1567212637, 1528468898, 1490877158, 1454394309, 1418979224, 1384592654, 1351197125, 1318756848, 1287237629, 1256606785, 1226833068, 1197886589, 1169738750, 1142362181, 1115730674, 1089819124, 1064603482, 1040060694, 1016168657, 992906171, 970252895, 948189308, 926696667, 905756971, 885352927, 865467914, 846085955, 827191686, 808770325, 790807650, 773289972, 756204106, 739537358, 723277495, 707412727, 691931689, 676823421, 662077351, 647683277, 633631353, 619912073, 606516257, 593435037, 580659842, 568182391, 555994676, 544088953, 532457731, 521093762, 509990030, 499139746, 488536332, 478173420, 468044839, 458144610, 448466936, 439006200, 429756952, 420713907, 411871938, 403226070, 394771472, 386503458, 378417476, 370509103, 362774046, 355208132, 347807307, 340567629, 333485267, 326556495, 319777692, 313145332, 306655988, 300306323, 294093093, 288013136, 282063378, 276240822, 270542554, 264965731]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 578).prefactor = (4682419641117237/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 578).cutoff/(generalMeanRows 578).c)).2 =
    (94427157206863/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 578).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 578).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 578).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 578

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 578).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 578).criticalRate j.val*(generalMeanRows 578).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 578).c*(generalMeanRows 578).criticalPoint j.val)).2-
      (generalMeanRows 578).J/2-(generalMeanRows 578).error (generalMeanGrid j.val)+
      (generalMeanRows 578).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 578).c)).2-
      (generalMeanRows 578).J/2-(generalMeanRows 578).error 4 := by
  have he : (generalMeanRows 578).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 578) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 578)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0578

/-! Kernel-checked entropy margins for general spectral rectangle 579. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0579
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5029605557, 4859062492, 4696106944, 4540307937, 4391264879, 4248604906, 4111980522, 3981067478, 3855562874, 3735183451, 3619664042, 3508756185, 3402226854, 3299857308, 3201442050, 3106787869, 3015712969, 2928046173, 2843626187, 2762300929, 2683926915, 2608368684, 2535498273, 2465194738, 2397343699, 2331836926, 2268571957, 2207451740, 2148384300, 2091282431, 2036063412, 1982648737, 1930963870, 1880938007, 1832503865, 1785597479, 1740158009, 1696127566, 1653451047, 1612075980, 1571952374, 1533032591, 1495271210, 1458624911, 1423052362, 1388514113, 1354972497, 1322391533, 1290736841, 1259975560, 1230076265, 1201008899, 1172744700, 1145256135, 1118516841, 1092501567, 1067186113, 1042547286, 1018562845, 995211459, 972472660, 950326800, 928755018, 907739196, 887261930, 867306491, 847856797, 828897382, 810413368, 792390439, 774814814, 757673223, 740952885, 724641486, 708727158, 693198461, 678044361, 663254215, 648817756, 634725071, 620966591, 607533076, 594415600, 581605537, 569094550, 556874580, 544937833, 533276770, 521884096, 510752753, 499875906, 489246939, 478859443, 468707208, 458784220, 449084648, 439602838, 430333309, 421270746, 412409991, 403746039, 395274035, 386989263, 378887146, 370963238, 363213222, 355632902, 348218201, 340965158, 333869922, 326928748, 320137994, 313494119, 306993678, 300633318, 294409778, 288319883, 282360543, 276528748, 270821570, 265236154]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 579).prefactor = (4685250061506981/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 579).cutoff/(generalMeanRows 579).c)).2 =
    (18743183834761/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 579).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 579).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 579).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 579

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 579).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 579).criticalRate j.val*(generalMeanRows 579).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 579).c*(generalMeanRows 579).criticalPoint j.val)).2-
      (generalMeanRows 579).J/2-(generalMeanRows 579).error (generalMeanGrid j.val)+
      (generalMeanRows 579).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 579).c)).2-
      (generalMeanRows 579).J/2-(generalMeanRows 579).error 4 := by
  have he : (generalMeanRows 579).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 579) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 579)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0579

/-! Kernel-checked entropy margins for general spectral rectangle 580. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0580
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4964600428, 4793933728, 4630889629, 4475035427, 4325968892, 4183315611, 4046726617, 3915876265, 3790460328, 3670194279, 3554811749, 3444063126, 3337714286, 3235545440, 3137350089, 3042934062, 2952114646, 2864719781, 2780587332, 2699564408, 2621506748, 2546278145, 2473749925, 2403800452, 2336314688, 2271183770, 2208304626, 2147579616, 2088916202, 2032226637, 1977427679, 1924440319, 1873189538, 1823604069, 1775616184, 1729161484, 1684178719, 1640609602, 1598398646, 1557493012, 1517842355, 1479398696, 1442116286, 1405951492, 1370862679, 1336810105, 1303755823, 1271663585, 1240498752, 1210228215, 1180820312, 1152244757, 1124472568, 1097476004, 1071228499, 1045704608, 1020879947, 996731146, 973235793, 950372395, 928120328, 906459797, 885371798, 864838078, 844841102, 825364018, 806390628, 787905352, 769893207, 752339775, 735231178, 718554054, 702295538, 686443231, 670985189, 655909897, 641206253, 626863549, 612871454, 599219999, 585899562, 572900851, 560214891, 547833014, 535746841, 523948276, 512429490, 501182910, 490201213, 479477314, 469004352, 458775690, 448784900, 439025754, 429492222, 420178460, 411078804, 402187763, 393500014, 385010394, 376713895, 368605658, 360680967, 352935246, 345364053, 337963071, 330728112, 323655105, 316740096, 309979243, 303368810, 296905168, 290584786, 284404233, 278360171, 272449352, 266668618, 261014894, 255485189, 250076592, 244786267]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 580).prefactor = (235085211941433/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 580).cutoff/(generalMeanRows 580).c)).2 =
    (367400955493631/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 580).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 580).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 580).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 580

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 580).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 580).criticalRate j.val*(generalMeanRows 580).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 580).c*(generalMeanRows 580).criticalPoint j.val)).2-
      (generalMeanRows 580).J/2-(generalMeanRows 580).error (generalMeanGrid j.val)+
      (generalMeanRows 580).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 580).c)).2-
      (generalMeanRows 580).J/2-(generalMeanRows 580).error 4 := by
  have he : (generalMeanRows 580).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 580) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 580)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0580

/-! Kernel-checked entropy margins for general spectral rectangle 581. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0581
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4944700865, 4774662314, 4612232353, 4456978108, 4308497234, 4166415250, 4030383163, 3900075339, 3775187600, 3655435499, 3540552775, 3430289949, 3324413053, 3222702475, 3124951909, 3030967393, 2940566437, 2853577216, 2769837835, 2689195658, 2611506681, 2536634962, 2464452093, 2394836710, 2327674047, 2262855515, 2200278315, 2139845084, 2081463553, 2025046249, 1970510195, 1917776651, 1866770859, 1817421813, 1769662037, 1723427387, 1678656857, 1635292404, 1593278779, 1552563373, 1513096072, 1474829117, 1437716979, 1401716235, 1366785457, 1332885107, 1299977434, 1268026379, 1236997492, 1206857843, 1177575946, 1149121687, 1121466249, 1094582051, 1068442685, 1043022856, 1018298327, 994245868, 970843208, 948068985, 925902703, 904324693, 883316070, 862858699, 842935157, 823528700, 804623235, 786203285, 768253963, 750760945, 733710446, 717089192, 700884400, 685083755, 669675392, 654647871, 639990164, 625691632, 611742014, 598131406, 584850248, 571889308, 559239673, 546892727, 534840148, 523073891, 511586176, 500369481, 489416528, 478720275, 468273907, 458070826, 448104643, 438369171, 428858415, 419566566, 410487994, 401617242, 392949016, 384478185, 376199768, 368108935, 360200998, 352471404, 344915736, 337529702, 330309136, 323249989, 316348327, 309600329, 303002279, 296550564, 290241675, 284072194, 278038800, 272138263, 266367438, 260723266, 255202770, 249803050, 244521286]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 581).prefactor = (4698727855846389/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 581).cutoff/(generalMeanRows 581).c)).2 =
    (185122953812931/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 581).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 581).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 581).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 581

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 581).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 581).criticalRate j.val*(generalMeanRows 581).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 581).c*(generalMeanRows 581).criticalPoint j.val)).2-
      (generalMeanRows 581).J/2-(generalMeanRows 581).error (generalMeanGrid j.val)+
      (generalMeanRows 581).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 581).c)).2-
      (generalMeanRows 581).J/2-(generalMeanRows 581).error 4 := by
  have he : (generalMeanRows 581).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 581) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 581)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0581

/-! Kernel-checked entropy margins for general spectral rectangle 582. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0582
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4961922568, 4791291797, 4628296115, 4472501141, 4323503130, 4180926294, 4044420425, 3913658758, 3788336052, 3668166871, 3552884026, 3442237170, 3335991520, 3233926698, 3135835681, 3041523830, 2950808020, 2863515827, 2779484794, 2698561752, 2620602195, 2545469708, 2473035436, 2403177592, 2335781011, 2270736725, 2207941578, 2147297866, 2088713001, 2032099202, 1977373207, 1924456000, 1873272562, 1823751640, 1775825523, 1729429844, 1684503385, 1640987899, 1598827947, 1557970735, 1518365975, 1479965741, 1442724347, 1406598217, 1371545781, 1337527360, 1304505074, 1272442738, 1241305781, 1211061160, 1181677279, 1153123918, 1125372160, 1098394328, 1072163922, 1046655559, 1021844918, 997708688, 974224520, 951370977, 929127493, 907474330, 886392537, 865863916, 845870982, 826396936, 807425626, 788941521, 770929684, 753375741, 736265857, 719586713, 703325482, 687469806, 672007778, 656927918, 642219160, 627870829, 613872626, 600214614, 586887200, 573881119, 561187426, 548797478, 536702922, 524895685, 513367960, 502112198, 491121098, 480387591, 469904840, 459666223, 449665329, 439895950, 430352069, 421027858, 411917667, 403016019, 394317603, 385817269, 377510020, 369391008, 361455528, 353699013, 346117029, 338705271, 331459556, 324375823, 317450124, 310678624, 304057593, 297583409, 291252546, 285061578, 279007171, 273086083, 267295159, 261631329, 256091605, 250673079, 245372920]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 582).prefactor = (4715092869813547/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 582).cutoff/(generalMeanRows 582).c)).2 =
    (185122953812931/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 582).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 582).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 582).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 582

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 582).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 582).criticalRate j.val*(generalMeanRows 582).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 582).c*(generalMeanRows 582).criticalPoint j.val)).2-
      (generalMeanRows 582).J/2-(generalMeanRows 582).error (generalMeanGrid j.val)+
      (generalMeanRows 582).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 582).c)).2-
      (generalMeanRows 582).J/2-(generalMeanRows 582).error 4 := by
  have he : (generalMeanRows 582).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 582) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 582)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0582

/-! Kernel-checked entropy margins for general spectral rectangle 583. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0583
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4900863609, 4730105091, 4567003882, 4411125516, 4262066100, 4119449647, 3982925695, 3852167181, 3726868530, 3606743933, 3491525801, 3380963356, 3274821364, 3172878977, 3074928680, 2980775336, 2890235304, 2803135638, 2719313352, 2638614743, 2560894767, 2486016473, 2413850465, 2344274423, 2277172645, 2212435635, 2149959711, 2089646650, 2031403351, 1975141528, 1920777419, 1868231520, 1817428331, 1768296126, 1720766735, 1674775336, 1630260269, 1587162857, 1545427237, 1505000206, 1465831075, 1427871530, 1391075502, 1355399051, 1320800247, 1287239065, 1254677287, 1223078404, 1192407529, 1162631311, 1133717861, 1105636672, 1078358552, 1051855559, 1026100934, 1001069048, 976735341, 953076273, 930069275, 907692697, 885925770, 864748560, 844141929, 824087498, 804567611, 785565303, 767064266, 749048818, 731503876, 714414932, 697768018, 681549692, 665747007, 650347495, 635339139, 620710360, 606449996, 592547280, 578991830, 565773625, 552882998, 540310613, 528047457, 516084824, 504414302, 493027765, 481917355, 471075476, 460494781, 450168164, 440088749, 430249883, 420645123, 411268234, 402113174, 393174092, 384445322, 375921367, 367596905, 359466771, 351525961, 343769618, 336193032, 328791633, 321560985, 314496784, 307594849, 300851121, 294261660, 287822636, 281530328, 275381124, 269371508, 263498068, 257757482, 252146524, 246662053, 241301017, 236060446, 230937450, 225929216]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 583).prefactor = (2359108100871473/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 583).cutoff/(generalMeanRows 583).c)).2 =
    (44999189276971/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 583).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 583).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 583).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 583

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 583).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 583).criticalRate j.val*(generalMeanRows 583).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 583).c*(generalMeanRows 583).criticalPoint j.val)).2-
      (generalMeanRows 583).J/2-(generalMeanRows 583).error (generalMeanGrid j.val)+
      (generalMeanRows 583).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 583).c)).2-
      (generalMeanRows 583).J/2-(generalMeanRows 583).error 4 := by
  have he : (generalMeanRows 583).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 583) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 583)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0583

/-! Kernel-checked entropy margins for general spectral rectangle 584. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0584
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5285241377, 5118417221, 4958917081, 4806320255, 4660235969, 4520300765, 4386176164, 4257546580, 4134117440, 4015613496, 3901777306, 3792367849, 3687159276, 3585939778, 3488510550, 3394684844, 3304287113, 3217152216, 3133124701, 3052058133, 2973814489, 2898263589, 2825282586, 2754755476, 2686572664, 2620630549, 2556831147, 2495081735, 2435294530, 2377386379, 2321278480, 2266896120, 2214168426, 2163028142, 2113411411, 2065257580, 2018509011, 1973110910, 1929011163, 1886160187, 1844510781, 1804018000, 1764639025, 1726333049, 1689061164, 1652786260, 1617472926, 1583087360, 1549597282, 1516971856, 1485181610, 1454198370, 1423995185, 1394546272, 1365826951, 1337813589, 1310483549, 1283815138, 1257787561, 1232380877, 1207575953, 1183354429, 1159698677, 1136591769, 1114017437, 1091960049, 1070404574, 1049336554, 1028742079, 1008607759, 988920704, 969668494, 950839165, 932421184, 914403431, 896775178, 879526077, 862646137, 846125714, 829955490, 814126465, 798629938, 783457498, 768601011, 754052607, 739804669, 725849824, 712180934, 698791083, 685673570, 672821900, 660229779, 647891098, 635799936, 623950544, 612337345, 600954922, 589798015, 578861517, 568140462, 557630026, 547325520, 537222383, 527316180, 517602596, 508077433, 498736605, 489576134, 480592146, 471780870, 463138631, 454661848, 446347034, 438190786, 430189791, 422340816, 414640706, 407086389, 399674863, 392403200, 385268544]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 584).prefactor = (574307420401741/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 584).cutoff/(generalMeanRows 584).c)).2 =
    (210290722998737/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 584).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 584).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 584).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 584

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 584).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 584).criticalRate j.val*(generalMeanRows 584).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 584).c*(generalMeanRows 584).criticalPoint j.val)).2-
      (generalMeanRows 584).J/2-(generalMeanRows 584).error (generalMeanGrid j.val)+
      (generalMeanRows 584).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 584).c)).2-
      (generalMeanRows 584).J/2-(generalMeanRows 584).error 4 := by
  have he : (generalMeanRows 584).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 584) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 584)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0584

/-! Kernel-checked entropy margins for general spectral rectangle 585. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0585
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4870467926, 4698457110, 4534241899, 4377376904, 4227448171, 4084070444, 3946884715, 3815556035, 3689771551, 3569238738, 3453683798, 3342850219, 3236497469, 3134399797, 3036345161, 2942134230, 2851579489, 2764504406, 2680742676, 2600137527, 2522541076, 2447813739, 2375823692, 2306446361, 2239563963, 2175065074, 2112844231, 2052801559, 1994842435, 1938877161, 1884820672, 1832592258, 1782115305, 1733317059, 1686128399, 1640483625, 1596320269, 1553578905, 1512202982, 1472138662, 1433334671, 1395742155, 1359314553, 1324007465, 1289778545, 1256587383, 1224395408, 1193165787, 1162863338, 1133454440, 1104906955, 1077190151, 1050274631, 1024132265, 998736126, 974060429, 950080477, 926772605, 904114128, 882083299, 860659255, 839821984, 819552276, 799831690, 780642515, 761967738, 743791010, 726096614, 708869440, 692094953, 675759169, 659848628, 644350376, 629251935, 614541287, 600206852, 586237468, 572622378, 559351203, 546413935, 533800916, 521502826, 509510667, 497815749, 486409679, 475284350, 464431924, 453844827, 443515735, 433437565, 423603466, 414006807, 404641173, 395500353, 386578332, 377869287, 369367576, 361067732, 352964458, 345052620, 337327238, 329783486, 322416681, 315222281, 308195879, 301333198, 294630086, 288082513, 281686565, 275438442, 269334452, 263371008, 257544624, 251851915, 246289587, 240854441, 235543365, 230353332, 225281400, 220324705, 215480464]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 585).prefactor = (4792615910112733/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 585).cutoff/(generalMeanRows 585).c)).2 =
    (181060250090973/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 585).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 585).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 585).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 585

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 585).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 585).criticalRate j.val*(generalMeanRows 585).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 585).c*(generalMeanRows 585).criticalPoint j.val)).2-
      (generalMeanRows 585).J/2-(generalMeanRows 585).error (generalMeanGrid j.val)+
      (generalMeanRows 585).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 585).c)).2-
      (generalMeanRows 585).J/2-(generalMeanRows 585).error 4 := by
  have he : (generalMeanRows 585).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 585) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 585)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0585

/-! Kernel-checked entropy margins for general spectral rectangle 586. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0586
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4986164821, 4812421803, 4646520992, 4488014141, 4336484671, 4191544907, 4052833614, 3920013790, 3792770687, 3670810031, 3553856407, 3441651811, 3333954324, 3230536920, 3131186370, 3035702248, 2943896019, 2855590208, 2770617639, 2688820724, 2610050829, 2534167672, 2461038775, 2390538963, 2322549892, 2256959615, 2193662183, 2132557270, 2073549831, 2016549776, 1961471675, 1908234476, 1856761249, 1806978942, 1758818155, 1712212931, 1667100557, 1623421381, 1581118638, 1540138291, 1500428878, 1461941368, 1424629032, 1388447316, 1353353724, 1319307708, 1286270562, 1254205329, 1223076706, 1192850960, 1163495844, 1134980522, 1107275500, 1080352551, 1054184657, 1028745947, 1004011637, 979957980, 956562215, 933802513, 911657941, 890108410, 869134641, 848718122, 828841075, 809486420, 790637741, 772279257, 754395793, 736972752, 719996086, 703452275, 687328302, 671611630, 656290178, 641352308, 626786799, 612582832, 598729970, 585218147, 572037645, 559179085, 546633411, 534391874, 522446025, 510787694, 499408989, 488302276, 477460173, 466875539, 456541464, 446451260, 436598454, 426976775, 417580153, 408402705, 399438732, 390682708, 382129279, 373773253, 365609593, 357633413, 349839976, 342224679, 334783060, 327510784, 320403642, 313457547, 306668528, 300032727, 293546397, 287205894, 281007676, 274948301, 269024421, 263232779, 257570209, 252033628, 246620040, 241326526, 236150246]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 586).prefactor = (1206461031885843/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 586).cutoff/(generalMeanRows 586).c)).2 =
    (73916644276707/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 586).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 586).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 586).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 586

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 586).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 586).criticalRate j.val*(generalMeanRows 586).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 586).c*(generalMeanRows 586).criticalPoint j.val)).2-
      (generalMeanRows 586).J/2-(generalMeanRows 586).error (generalMeanGrid j.val)+
      (generalMeanRows 586).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 586).c)).2-
      (generalMeanRows 586).J/2-(generalMeanRows 586).error 4 := by
  have he : (generalMeanRows 586).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 586) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 586)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0586

/-! Kernel-checked entropy margins for general spectral rectangle 587. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0587
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5259536161, 5091174654, 4930266035, 4776380484, 4629118803, 4488109745, 4353007620, 4223490162, 4099256609, 3980025970, 3865535473, 3755539146, 3649806544, 3548121580, 3450281471, 3356095769, 3265385481, 3177982258, 3093727655, 3012472451, 2934076023, 2858405768, 2785336575, 2714750330, 2646535465, 2580586539, 2516803845, 2455093056, 2395364882, 2337534767, 2281522595, 2227252423, 2174652227, 2123653674, 2074191900, 2026205306, 1979635372, 1934426474, 1890525723, 1847882806, 1806449843, 1766181247, 1727033601, 1688965535, 1651937612, 1615912228, 1580853505, 1546727207, 1513500643, 1481142591, 1449623220, 1418914013, 1388987702, 1359818204, 1331380556, 1303650861, 1276606232, 1250224743, 1224485377, 1199367985, 1174853242, 1150922602, 1127558265, 1104743140, 1082460808, 1060695493, 1039432026, 1018655825, 998352857, 978509623, 959113122, 940150839, 921610713, 903481124, 885750867, 868409139, 851445516, 834849939, 818612698, 802724416, 787176033, 771958798, 757064247, 742484199, 728210740, 714236212, 700553204, 687154540, 674033271, 661182665, 648596198, 636267546, 624190579, 612359349, 600768088, 589411197, 578283241, 567378944, 556693181, 546220975, 535957489, 525898020, 516037999, 506372980, 496898642, 487610778, 478505296, 469578213, 460825652, 452243838, 443829092, 435577833, 427486571, 419551904, 411770519, 404139183, 396654745, 389314133, 382114347, 375052465, 368125633]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 587).prefactor = (4655449209567267/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 587).cutoff/(generalMeanRows 587).c)).2 =
    (419590669047169/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 587).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 587).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 587).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 587

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 587).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 587).criticalRate j.val*(generalMeanRows 587).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 587).c*(generalMeanRows 587).criticalPoint j.val)).2-
      (generalMeanRows 587).J/2-(generalMeanRows 587).error (generalMeanGrid j.val)+
      (generalMeanRows 587).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 587).c)).2-
      (generalMeanRows 587).J/2-(generalMeanRows 587).error 4 := by
  have he : (generalMeanRows 587).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 587) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 587)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0587

/-! Kernel-checked entropy margins for general spectral rectangle 588. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0588
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5277264415, 5108335414, 4946884422, 4792480170, 4644722117, 4503237761, 4367680249, 4237726228, 4113073922, 3993441395, 3878564986, 3768197896, 3662108902, 3560081190, 3461911292, 3367408120, 3276392076, 3188694244, 3104155644, 3022626555, 2943965876, 2868040561, 2794725074, 2723900905, 2655456110, 2589284890, 2525287205, 2463368408, 2403438909, 2345413867, 2289212896, 2234759795, 2181982301, 2130811848, 2081183353, 2033035012, 1986308104, 1940946821, 1896898094, 1854111442, 1812538821, 1772134492, 1732854892, 1694658510, 1657505778, 1621358963, 1586182069, 1551940741, 1518602181, 1486135060, 1454509447, 1423696729, 1393669546, 1364401727, 1335868224, 1308045061, 1280909273, 1254438860, 1228612735, 1203410680, 1178813305, 1154802002, 1131358912, 1108466884, 1086109446, 1064270766, 1042935627, 1022089395, 1001717993, 981807873, 962345993, 943319794, 924717175, 906526476, 888736457, 871336275, 854315473, 837663957, 821371986, 805430149, 789829358, 774560830, 759616074, 744986881, 730665311, 716643679, 702914550, 689470723, 676305226, 663411305, 650782413, 638412205, 626294531, 614423422, 602793090, 591397918, 580232453, 569291401, 558569620, 548062116, 537764034, 527670658, 517777402, 508079805, 498573532, 489254361, 480118188, 471161015, 462378952, 453768210, 445325101, 437046029, 428927494, 420966083, 413158469, 405501410, 397991745, 390626389, 383402336, 376316650, 369366470]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 588).prefactor = (4671141274907949/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 588).cutoff/(generalMeanRows 588).c)).2 =
    (419590669047169/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 588).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 588).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 588).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 588

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 588).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 588).criticalRate j.val*(generalMeanRows 588).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 588).c*(generalMeanRows 588).criticalPoint j.val)).2-
      (generalMeanRows 588).J/2-(generalMeanRows 588).error (generalMeanGrid j.val)+
      (generalMeanRows 588).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 588).c)).2-
      (generalMeanRows 588).J/2-(generalMeanRows 588).error 4 := by
  have he : (generalMeanRows 588).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 588) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 588)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0588

/-! Kernel-checked entropy margins for general spectral rectangle 589. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0589
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5120275667, 4951400768, 4790038721, 4635758200, 4488158506, 4346866896, 4211536195, 4081842656, 3957484045, 3838177914, 3723660041, 3613683019, 3508014980, 3406438433, 3308749202, 3214755469, 3124276885, 3037143764, 2953196347, 2872284116, 2794265174, 2719005666, 2646379250, 2576266605, 2508554977, 2443137765, 2379914123, 2318788610, 2259670847, 2202475211, 2147120542, 2093529881, 2041630209, 1991352222, 1942630108, 1895401348, 1849606520, 1805189124, 1762095418, 1720274258, 1679676955, 1640257137, 1601970623, 1564775299, 1528631008, 1493499444, 1459344051, 1426129932, 1393823757, 1362393685, 1331809281, 1302041449, 1273062354, 1244845369, 1217365001, 1190596843, 1164517514, 1139104608, 1114336649, 1090193042, 1066654029, 1043700651, 1021314706, 999478716, 978175890, 957390091, 937105807, 917308121, 897982681, 879115678, 860693817, 842704295, 825134780, 807973388, 791208664, 774829561, 758825426, 743185978, 727901293, 712961792, 698358223, 684081646, 670123423, 656475204, 643128914, 630076742, 617311132, 604824770, 592610575, 580661691, 568971477, 557533498, 546341517, 535389489, 524671551, 514182017, 503915370, 493866258, 484029483, 474400001, 464972913, 455743460, 446707018, 437859093, 429195319, 420711450, 412403355, 404267021, 396298538, 388494107, 380850028, 373362699, 366028614, 358844359, 351806609, 344912125, 338157751, 331540412, 325057110, 318704925, 312481007]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 589).prefactor = (1168489071198761/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 589).cutoff/(generalMeanRows 589).c)).2 =
    (25086687421333/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 589).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 589).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 589).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 589

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 589).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 589).criticalRate j.val*(generalMeanRows 589).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 589).c*(generalMeanRows 589).criticalPoint j.val)).2-
      (generalMeanRows 589).J/2-(generalMeanRows 589).error (generalMeanGrid j.val)+
      (generalMeanRows 589).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 589).c)).2-
      (generalMeanRows 589).J/2-(generalMeanRows 589).error 4 := by
  have he : (generalMeanRows 589).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 589) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 589)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0589

/-! Kernel-checked entropy margins for general spectral rectangle 590. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0590
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5225434593, 5055620582, 4893335038, 4738145295, 4589649436, 4447473615, 4311269653, 4180712899, 4055500296, 3935348652, 3819993072, 3709185545, 3602693654, 3500299415, 3401798213, 3306997830, 3215717564, 3127787414, 3043047340, 2961346576, 2882543007, 2806502587, 2733098807, 2662212202, 2593729897, 2527545185, 2463557135, 2401670235, 2341794050, 2283842912, 2227735633, 2173395230, 2120748675, 2069726661, 2020263384, 1972296333, 1925766108, 1880616235, 1836792998, 1794245289, 1752924457, 1712784171, 1673780292, 1635870754, 1599015448, 1563176118, 1528316260, 1494401027, 1461397143, 1429272820, 1397997678, 1367542673, 1337880025, 1308983158, 1280826634, 1253386095, 1226638213, 1200560633, 1175131926, 1150331544, 1126139779, 1102537714, 1079507194, 1057030781, 1035091727, 1013673934, 992761928, 972340828, 952396317, 932914620, 913882472, 895287102, 877116205, 859357924, 842000828, 825033895, 808446492, 792228359, 776369591, 760860625, 745692224, 730855462, 716341713, 702142638, 688250171, 674656509, 661354101, 648335638, 635594044, 623122464, 610914257, 598962988, 587262419, 575806500, 564589365, 553605323, 542848849, 532314583, 521997321, 511892006, 501993728, 492297718, 482799337, 473494080, 464377563, 455445526, 446693823, 438118420, 429715392, 421480920, 413411283, 405502861, 397752126, 390155643, 382710064, 375412127, 368258652, 361246541, 354372772, 347634398, 341028546]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 590).prefactor = (4689839073418193/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 590).cutoff/(generalMeanRows 590).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 590).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 590).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 590).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 590

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 590).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 590).criticalRate j.val*(generalMeanRows 590).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 590).c*(generalMeanRows 590).criticalPoint j.val)).2-
      (generalMeanRows 590).J/2-(generalMeanRows 590).error (generalMeanGrid j.val)+
      (generalMeanRows 590).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 590).c)).2-
      (generalMeanRows 590).J/2-(generalMeanRows 590).error 4 := by
  have he : (generalMeanRows 590).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 590) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 590)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0590

/-! Kernel-checked entropy margins for general spectral rectangle 591. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0591
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5172651587, 5002049247, 4839036608, 4683177932, 4534068423, 4391331524, 4254616509, 4123596319, 3997965629, 3877439102, 3761749811, 3650647821, 3543898891, 3441283304, 3342594799, 3247639593, 3156235492, 3068211076, 2983404950, 2901665058, 2822848051, 2746818705, 2673449384, 2602619548, 2534215290, 2468128917, 2404258554, 2342507780, 2282785294, 2225004596, 2169083699, 2114944852, 2062514291, 2011722005, 1962501507, 1914789638, 1868526369, 1823654623, 1780120106, 1737871152, 1696858574, 1657035527, 1618357375, 1580781575, 1544267560, 1508776631, 1474271858, 1440717988, 1408081350, 1376329775, 1345432520, 1315360188, 1286084664, 1257579043, 1229817575, 1202775602, 1176429504, 1150756647, 1125735334, 1101344759, 1077564963, 1054376791, 1031761858, 1009702505, 988181770, 967183350, 946691576, 926691377, 907168255, 888108259, 869497958, 851324419, 833575183, 816238246, 799302033, 782755387, 766587543, 750788117, 735347083, 720254765, 705501814, 691079200, 676978197, 663190369, 649707558, 636521874, 623625683, 611011596, 598672460, 586601350, 574791555, 563236576, 551930111, 540866053, 530038480, 519441647, 509069981, 498918075, 488980679, 479252696, 469729177, 460405315, 451276438, 442338007, 433585610, 425014958, 416621879, 408402317, 400352324, 392468061, 384745789, 377181871, 369772765, 362515022, 355405282, 348440273, 341616808, 334931779, 328382159, 321964996, 315677413]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 591).prefactor = (59022084377519/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 591).cutoff/(generalMeanRows 591).c)).2 =
    (25086687421333/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 591).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 591).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 591).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 591

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 591).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 591).criticalRate j.val*(generalMeanRows 591).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 591).c*(generalMeanRows 591).criticalPoint j.val)).2-
      (generalMeanRows 591).J/2-(generalMeanRows 591).error (generalMeanGrid j.val)+
      (generalMeanRows 591).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 591).c)).2-
      (generalMeanRows 591).J/2-(generalMeanRows 591).error 4 := by
  have he : (generalMeanRows 591).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 591) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 591)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0591

/-! Kernel-checked entropy margins for general spectral rectangle 592. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0592
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5105068016, 4929607956, 4762036411, 4601902238, 4448786192, 4302298147, 4162074610, 4027776497, 3899087143, 3775710498, 3657369513, 3543804671, 3434772655, 3330045147, 3229407721, 3132658841, 3039608950, 2950079622, 2863902798, 2780920079, 2700982070, 2623947789, 2549684109, 2478065250, 2408972307, 2342292814, 2277920338, 2215754106, 2155698655, 2097663509, 2041562875, 1987315369, 1934843749, 1884074672, 1834938468, 1787368929, 1741303107, 1696681132, 1653446033, 1611543584, 1570922142, 1531532510, 1493327804, 1456263321, 1420296427, 1385386445, 1351494547, 1318583660, 1286618373, 1255564849, 1225390743, 1196065128, 1167558420, 1139842307, 1112889693, 1086674626, 1061172252, 1036358750, 1012211290, 988707979, 965827816, 943550652, 921857146, 900728726, 880147557, 860096500, 840559084, 821519474, 802962440, 784873329, 767238044, 750043009, 733275157, 716921897, 700971099, 685411072, 670230544, 655418646, 640964890, 626859159, 613091684, 599653036, 586534107, 573726098, 561220508, 549009119, 537083985, 525437422, 514061996, 502950516, 492096020, 481491768, 471131235, 461008100, 451116239, 441449719, 432002786, 422769865, 413745549, 404924592, 396301906, 387872553, 379631741, 371574817, 363697266, 355994699, 348462856, 341097596, 333894896, 326850846, 319961646, 313223599, 306633112, 300186689, 293880930, 287712527, 281678260, 275774996, 269999686, 264349359, 258821125]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 592).prefactor = (2429651361608601/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 592).cutoff/(generalMeanRows 592).c)).2 =
    (188551026898781/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 592).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 592).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 592).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 592

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 592).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 592).criticalRate j.val*(generalMeanRows 592).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 592).c*(generalMeanRows 592).criticalPoint j.val)).2-
      (generalMeanRows 592).J/2-(generalMeanRows 592).error (generalMeanGrid j.val)+
      (generalMeanRows 592).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 592).c)).2-
      (generalMeanRows 592).J/2-(generalMeanRows 592).error 4 := by
  have he : (generalMeanRows 592).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 592) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 592)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0592

/-! Kernel-checked entropy margins for general spectral rectangle 593. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0593
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5227274246, 5050114452, 4880889204, 4719144414, 4564458136, 4416437754, 4274717485, 4138956134, 4008835087, 3884056501, 3764341668, 3649429537, 3539075379, 3433049565, 3331136460, 3233133409, 3138849819, 3048106306, 2960733924, 2876573451, 2795474733, 2717296083, 2641903721, 2569171263, 2498979243, 2431214675, 2365770647, 2302545939, 2241444674, 2182375993, 2125253749, 2069996227, 2016525878, 1964769078, 1914655893, 1866119869, 1819097832, 1773529700, 1729358309, 1686529248, 1644990704, 1604693325, 1565590076, 1527636119, 1490788692, 1455006996, 1420252093, 1386486804, 1353675620, 1321784610, 1290781343, 1260634809, 1231315345, 1202794568, 1175045310, 1148041553, 1121758379, 1096171907, 1071259247, 1046998452, 1023368466, 1000349088, 977920925, 956065359, 934764503, 914001174, 893758853, 874021661, 854774323, 836002143, 817690978, 799827213, 782397734, 765389910, 748791569, 732590977, 716776821, 701338187, 686264548, 671545742, 657171960, 643133730, 629421900, 616027631, 602942377, 590157876, 577666140, 565459441, 553530302, 541871487, 530475989, 519337024, 508448023, 497802618, 487394642, 477218114, 467267236, 457536386, 448020110, 438713117, 429610272, 420706590, 411997232, 403477498, 395142824, 386988776, 379011043, 371205440, 363567894, 356094448, 348781252, 341624563, 334620739, 327766236, 321057605, 314491490, 308064623, 301773823, 295615992, 289588111, 283687242]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 593).prefactor = (4892993294395183/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 593).cutoff/(generalMeanRows 593).c)).2 =
    (384677847606021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 593).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 593).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 593).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 593

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 593).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 593).criticalRate j.val*(generalMeanRows 593).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 593).c*(generalMeanRows 593).criticalPoint j.val)).2-
      (generalMeanRows 593).J/2-(generalMeanRows 593).error (generalMeanGrid j.val)+
      (generalMeanRows 593).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 593).c)).2-
      (generalMeanRows 593).J/2-(generalMeanRows 593).error 4 := by
  have he : (generalMeanRows 593).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 593) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 593)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0593

/-! Kernel-checked entropy margins for general spectral rectangle 594. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0594
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5296824626, 5124690611, 4960187918, 4802877968, 4652353355, 4508235123, 4370170340, 4237829915, 4110906654, 3989113495, 3872181924, 3759860541, 3651913755, 3548120603, 3448273675, 3352178127, 3259650787, 3170519333, 3084621537, 3001804575, 2921924390, 2844845103, 2770438479, 2698583419, 2629165507, 2562076577, 2497214322, 2434481921, 2373787705, 2315044838, 2258171020, 2203088216, 2149722403, 2098003325, 2047864278, 1999241901, 1952075979, 1906309266, 1861887315, 1818758319, 1776872960, 1736184276, 1696647525, 1658220066, 1620861242, 1584532274, 1549196159, 1514817575, 1481362791, 1448799585, 1417097162, 1386226079, 1356158179, 1326866523, 1298325323, 1270509891, 1243396579, 1216962726, 1191186611, 1166047406, 1141525132, 1117600615, 1094255451, 1071471965, 1049233179, 1027522776, 1006325069, 985624975, 965407982, 945660125, 926367960, 907518539, 889099391, 871098495, 853504267, 836305531, 819491511, 803051805, 786976374, 771255524, 755879892, 740840429, 726128394, 711735331, 697653064, 683873685, 670389539, 657193218, 644277547, 631635580, 619260585, 607146037, 595285614, 583673184, 572302801, 561168694, 550265265, 539587080, 529128862, 518885488, 508851981, 499023503, 489395355, 479962969, 470721903, 461667836, 452796566, 444104006, 435586176, 427239204, 419059320, 411042853, 403186227, 395485960, 387938659, 380541017, 373289812, 366181901, 359214223, 352383789, 345687688]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 594).prefactor = (4753911785518663/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 594).cutoff/(generalMeanRows 594).c)).2 =
    (204510311798199/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 594).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 594).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 594).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 594

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 594).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 594).criticalRate j.val*(generalMeanRows 594).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 594).c*(generalMeanRows 594).criticalPoint j.val)).2-
      (generalMeanRows 594).J/2-(generalMeanRows 594).error (generalMeanGrid j.val)+
      (generalMeanRows 594).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 594).c)).2-
      (generalMeanRows 594).J/2-(generalMeanRows 594).error 4 := by
  have he : (generalMeanRows 594).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 594) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 594)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0594

/-! Kernel-checked entropy margins for general spectral rectangle 595. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0595
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5424441100, 5250800325, 5084832275, 4926095481, 4774179883, 4628704087, 4489312915, 4355675212, 4227481881, 4104444109, 3986291768, 3872771968, 3763647747, 3658696876, 3557710777, 3460493531, 3366860975, 3276639870, 3189667144, 3105789196, 3024861252, 2946746773, 2871316914, 2798450020, 2728031156, 2659951684, 2594108860, 2530405465, 2468749462, 2409053675, 2351235499, 2295216614, 2240922738, 2188283378, 2137231616, 2087703890, 2039639808, 1992981960, 1947675750, 1903669235, 1860912977, 1819359901, 1778965166, 1739686040, 1701481786, 1664313552, 1628144269, 1592938557, 1558662634, 1525284229, 1492772508, 1461097991, 1430232490, 1400149035, 1370821816, 1342226121, 1314338284, 1287135628, 1260596418, 1234699813, 1209425822, 1184755264, 1160669725, 1137151524, 1114183677, 1091749860, 1069834383, 1048422158, 1027498668, 1007049944, 987062537, 967523498, 948420349, 929741066, 911474059, 893608149, 876132552, 859036862, 842311033, 825945365, 809930486, 794257341, 778917178, 763901532, 749202220, 734811319, 720721166, 706924338, 693413651, 680182142, 667223065, 654529882, 642096255, 629916034, 617983256, 606292135, 594837051, 583612553, 572613344, 561834278, 551270359, 540916728, 530768662, 520821570, 511070986, 501512566, 492142082, 482955422, 473948580, 465117658, 456458858, 447968483, 439642928, 431478683, 423472326, 415620520, 407920014, 400367636, 392960293, 385694967, 378568713]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 595).prefactor = (4786275659111853/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 595).cutoff/(generalMeanRows 595).c)).2 =
    (208356484609779/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 595).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 595).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 595).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 595

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 595).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 595).criticalRate j.val*(generalMeanRows 595).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 595).c*(generalMeanRows 595).criticalPoint j.val)).2-
      (generalMeanRows 595).J/2-(generalMeanRows 595).error (generalMeanGrid j.val)+
      (generalMeanRows 595).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 595).c)).2-
      (generalMeanRows 595).J/2-(generalMeanRows 595).error 4 := by
  have he : (generalMeanRows 595).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 595) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 595)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0595

/-! Kernel-checked entropy margins for general spectral rectangle 596. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0596
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5130130847, 4960940149, 4799269539, 4644687770, 4496794199, 4355216109, 4219606332, 4089641109, 3965018173, 3845455028, 3730687390, 3620467775, 3514564231, 3412759166, 3314848303, 3220639707, 3129952909, 3042618100, 2958475389, 2877374124, 2799172271, 2723735835, 2650938333, 2580660301, 2512788842, 2447217210, 2383844418, 2322574879, 2263318074, 2205988237, 2150504072, 2096788477, 2044768300, 1994374103, 1945539942, 1898203167, 1852304229, 1807786505, 1764596129, 1722681839, 1681994829, 1642488613, 1604118899, 1566843464, 1530622046, 1495416236, 1461189380, 1427906480, 1395534115, 1364040351, 1333394664, 1303567870, 1274532055, 1246260505, 1218727653, 1191909014, 1165781133, 1140321534, 1115508671, 1091321883, 1067741347, 1044748041, 1022323705, 1000450802, 979112484, 958292561, 937975469, 918146239, 898790473, 879894312, 861444418, 843427945, 825832518, 808646212, 791857535, 775455402, 759429122, 743768381, 728463223, 713504034, 698881533, 684586750, 670611018, 656945959, 643583472, 630515722, 617735126, 605234349, 593006286, 581044059, 569341007, 557890675, 546686807, 535723338, 524994388, 514494255, 504217405, 494158470, 484312237, 474673648, 465237789, 455999888, 446955309, 438099546, 429428220, 420937073, 412621966, 404478872, 396503875, 388693163, 381043027, 373549858, 366210140, 359020452, 351977461, 345077920, 338318665, 331696616, 325208767, 318852192, 312624036]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 596).prefactor = (467536464812103/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 596).cutoff/(generalMeanRows 596).c)).2 =
    (399951248315223/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 596).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 596).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 596).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 596

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 596).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 596).criticalRate j.val*(generalMeanRows 596).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 596).c*(generalMeanRows 596).criticalPoint j.val)).2-
      (generalMeanRows 596).J/2-(generalMeanRows 596).error (generalMeanGrid j.val)+
      (generalMeanRows 596).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 596).c)).2-
      (generalMeanRows 596).J/2-(generalMeanRows 596).error 4 := by
  have he : (generalMeanRows 596).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 596) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 596)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0596

/-! Kernel-checked entropy margins for general spectral rectangle 597. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0597
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5138875446, 4969396354, 4807450167, 4652604905, 4504459240, 4362639822, 4226798891, 4096612135, 3971776772, 3852009825, 3737046558, 3626639068, 3520555005, 3418576408, 3320498650, 3226129470, 3135288092, 3047804416, 2963518278, 2882278771, 2803943619, 2728378598, 2655457008, 2585059183, 2517072034, 2451388631, 2387907816, 2326533840, 2267176028, 2209748470, 2154169728, 2100362572, 2048253724, 1997773627, 1948856225, 1901438762, 1855461587, 1810867980, 1767603983, 1725618248, 1684861885, 1645288329, 1606853211, 1569514237, 1533231078, 1497965258, 1463680060, 1430340428, 1397912883, 1366365435, 1335667511, 1305789876, 1276704567, 1248384827, 1220805044, 1193940691, 1167768273, 1142265277, 1117410119, 1093182103, 1069561373, 1046528874, 1024066314, 1002156127, 980781437, 959926025, 939574302, 919711272, 900322512, 881394142, 862912799, 844865616, 827240196, 810024596, 793207301, 776777210, 760723612, 745036177, 729704930, 714720243, 700072816, 685753667, 671754112, 658065761, 644680497, 631590472, 618788091, 606266005, 594017099, 582034482, 570311482, 558841631, 547618665, 536636509, 525889271, 515371240, 505076872, 495000791, 485137775, 475482756, 466030813, 456777166, 447717170, 438846312, 430160205, 421654584, 413325304, 405168329, 397179738, 389355712, 381692536, 374186595, 366834366, 359632423, 352577426, 345666125, 338895349, 332262012, 325763104, 319395694, 313156922]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 597).prefactor = (2341667036422991/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 597).cutoff/(generalMeanRows 597).c)).2 =
    (399951248315223/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 597).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 597).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 597).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 597

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 597).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 597).criticalRate j.val*(generalMeanRows 597).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 597).c*(generalMeanRows 597).criticalPoint j.val)).2-
      (generalMeanRows 597).J/2-(generalMeanRows 597).error (generalMeanGrid j.val)+
      (generalMeanRows 597).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 597).c)).2-
      (generalMeanRows 597).J/2-(generalMeanRows 597).error 4 := by
  have he : (generalMeanRows 597).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 597) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 597)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0597

/-! Kernel-checked entropy margins for general spectral rectangle 598. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0598
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5062977369, 4893583218, 4731738652, 4577011614, 4429000658, 4287332273, 4151658504, 4021654809, 3897018151, 3777465271, 3662731128, 3552567496, 3446741682, 3345035374, 3247243575, 3153173648, 3062644430, 2975485430, 2891536085, 2810645087, 2732669754, 2657475459, 2584935096, 2514928593, 2447342458, 2382069360, 2319007742, 2258061462, 2199139453, 2142155421, 2087027549, 2033678231, 1982033820, 1932024399, 1883583556, 1836648184, 1791158293, 1747056828, 1704289504, 1662804651, 1622553069, 1583487888, 1545564442, 1508740148, 1472974393, 1438228429, 1404465272, 1371649606, 1339747700, 1308727322, 1278557661, 1249209252, 1220653911, 1192864664, 1165815692, 1139482266, 1113840698, 1088868285, 1064543263, 1040844759, 1017752751, 995248021, 973312120, 951927331, 931076633, 910743671, 890912718, 871568654, 852696932, 834283553, 816315042, 798778424, 781661201, 764951330, 748637203, 732707628, 717151811, 701959340, 687120163, 672624580, 658463223, 644627041, 631107291, 617895524, 604983568, 592363524, 580027749, 567968847, 556179662, 544653264, 533382943, 522362199, 511584735, 501044447, 490735420, 480651916, 470788371, 461139388, 451699730, 442464314, 433428204, 424586609, 415934876, 407468483, 399183039, 391074275, 383138040, 375370302, 367767136, 360324727, 353039364, 345907434, 338925423, 332089910, 325397564, 318845143, 312429488, 306147524, 299996255, 293972760, 288074194]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 598).prefactor = (36599829454971/7812500000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 598).cutoff/(generalMeanRows 598).c)).2 =
    (195470881252459/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 598).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 598).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 598).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 598

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 598).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 598).criticalRate j.val*(generalMeanRows 598).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 598).c*(generalMeanRows 598).criticalPoint j.val)).2-
      (generalMeanRows 598).J/2-(generalMeanRows 598).error (generalMeanGrid j.val)+
      (generalMeanRows 598).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 598).c)).2-
      (generalMeanRows 598).J/2-(generalMeanRows 598).error 4 := by
  have he : (generalMeanRows 598).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 598) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 598)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0598

/-! Kernel-checked entropy margins for general spectral rectangle 599. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0599
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5071642805, 4901958731, 4739837163, 4584845305, 4436581024, 4294670170, 4158764190, 4028537990, 3903688014, 3783930515, 3669000001, 3558647820, 3452640883, 3350760501, 3252801329, 3158570399, 3067886237, 2980578061, 2896485035, 2815455589, 2737346800, 2662023808, 2589359290, 2519232968, 2451531157, 2386146342, 2322976793, 2261926201, 2202903346, 2145821784, 2090599559, 2037158931, 1985426130, 1935331116, 1886807365, 1839791662, 1794223914, 1750046967, 1707206446, 1665650591, 1625330117, 1586198075, 1548209721, 1511322402, 1475495433, 1440690000, 1406869056, 1373997225, 1342040718, 1310967248, 1280745950, 1251347311, 1222743096, 1194906288, 1167811020, 1141432524, 1115747069, 1090731915, 1066365260, 1042626196, 1019494665, 996951417, 974977972, 953556583, 932670199, 912302436, 892437542, 873060370, 854156348, 835711454, 817712189, 800145557, 782999038, 766260567, 749918518, 733961679, 718379238, 703160764, 688296190, 673775797, 659590202, 645730339, 632187450, 618953070, 606019016, 593377372, 581020484, 568940943, 557131580, 545585454, 534295843, 523256237, 512460327, 501902000, 491575328, 481474566, 471594139, 461928642, 452472828, 443221605, 434170029, 425313302, 416646761, 408165878, 399866253, 391743610, 383793792, 376012759, 368396580, 360941434, 353643601, 346499465, 339505504, 332658291, 325954492, 319390856, 312964221, 306671505, 300509707, 294475903, 288567242]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 599).prefactor = (4692796307142657/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 599).cutoff/(generalMeanRows 599).c)).2 =
    (195470881252459/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 599).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 599).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 599).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 599

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 599).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 599).criticalRate j.val*(generalMeanRows 599).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 599).c*(generalMeanRows 599).criticalPoint j.val)).2-
      (generalMeanRows 599).J/2-(generalMeanRows 599).error (generalMeanGrid j.val)+
      (generalMeanRows 599).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 599).c)).2-
      (generalMeanRows 599).J/2-(generalMeanRows 599).error 4 := by
  have he : (generalMeanRows 599).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 599) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 599)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0599

/-! Kernel-checked entropy margins for general spectral rectangle 600. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0600
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5089018196, 4918752786, 4756075791, 4600552933, 4451780700, 4309383661, 4173012070, 4042339716, 3917062005, 3796894218, 3681569954, 3570839707, 3464469592, 3362240169, 3263945390, 3169391625, 3078396781, 2990789488, 2906408360, 2825101308, 2746724919, 2671143871, 2598230405, 2527863832, 2459930075, 2394321253, 2330935285, 2269675535, 2210450468, 2153173345, 2097761929, 2044138215, 1992228178, 1941961539, 1893271546, 1846094767, 1800370904, 1756042608, 1713055316, 1671357091, 1630898480, 1591632371, 1553513870, 1516500175, 1480550463, 1445625788, 1411688973, 1378704524, 1346638534, 1315458607, 1285133771, 1255634412, 1226932200, 1199000023, 1171811928, 1145343059, 1119569606, 1094468750, 1070018615, 1046198222, 1022987442, 1000366961, 978318236, 956823457, 935865516, 915427974, 895495023, 876051465, 857082678, 838574592, 820513662, 802886847, 785681584, 768885767, 752487730, 736476223, 720840397, 705569785, 690654285, 676084146, 661849951, 647942604, 634353317, 621073597, 608095230, 595410276, 583011053, 570890128, 559040306, 547454624, 536126335, 525048907, 514216011, 503621510, 493259460, 483124092, 473209815, 463511204, 454022995, 444740077, 435657491, 426770420, 418074188, 409564250, 401236190, 393085719, 385108666, 377300975, 369658703, 362178015, 354855180, 347686568, 340668646, 333797975, 327071208, 320485085, 314036433, 307722158, 301539250, 295484774, 289555870]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 600).prefactor = (588609221785151/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 600).cutoff/(generalMeanRows 600).c)).2 =
    (195470881252459/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 600).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 600).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 600).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 600

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 600).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 600).criticalRate j.val*(generalMeanRows 600).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 600).c*(generalMeanRows 600).criticalPoint j.val)).2-
      (generalMeanRows 600).J/2-(generalMeanRows 600).error (generalMeanGrid j.val)+
      (generalMeanRows 600).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 600).c)).2-
      (generalMeanRows 600).J/2-(generalMeanRows 600).error 4 := by
  have he : (generalMeanRows 600).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 600) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 600)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0600

/-! Kernel-checked entropy margins for general spectral rectangle 601. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0601
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5081594046, 4911592427, 4749160566, 4593865745, 4445305880, 4303106849, 4166920106, 4036420540, 3911304563, 3791288382, 3676106440, 3565510011, 3459265920, 3357155380, 3258972941, 3164525523, 3073631534, 2986120065, 2901830151, 2820610090, 2742316821, 2666815347, 2593978203, 2523684969, 2455821819, 2390281093, 2326960919, 2265764846, 2206601512, 2149384334, 2094031214, 2040464278, 1988609619, 1938397062, 1889759952, 1842634946, 1796961824, 1752683307, 1709744897, 1668094717, 1627683364, 1588463776, 1550391098, 1513422567, 1477517395, 1442636663, 1408743225, 1375801609, 1343777930, 1312639809, 1282356292, 1252897780, 1224235954, 1196343715, 1169195118, 1142765318, 1117030511, 1091967885, 1067555568, 1043772585, 1020598815, 998014944, 976002431, 954543472, 933620959, 913218453, 893320151, 873910854, 854975941, 836501343, 818473517, 800879421, 783706493, 766942628, 750576161, 734595842, 718990823, 703750636, 688865182, 674324710, 660119804, 646241369, 632680619, 619429059, 606478480, 593820942, 581448763, 569354513, 557530999, 545971259, 534668548, 523616337, 512808297, 502238296, 491900389, 481788813, 471897977, 462222458, 452756996, 443496483, 434435962, 425570620, 416895781, 408406906, 400099582, 391969522, 384012557, 376224636, 368601819, 361140274, 353836274, 346686191, 339686496, 332833755, 326124622, 319555841, 313124243, 306826739, 300660320, 294622056, 288709090]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 601).prefactor = (4694276870953671/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 601).cutoff/(generalMeanRows 601).c)).2 =
    (9737753075837/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 601).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 601).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 601).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 601

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 601).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 601).criticalRate j.val*(generalMeanRows 601).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 601).c*(generalMeanRows 601).criticalPoint j.val)).2-
      (generalMeanRows 601).J/2-(generalMeanRows 601).error (generalMeanGrid j.val)+
      (generalMeanRows 601).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 601).c)).2-
      (generalMeanRows 601).J/2-(generalMeanRows 601).error 4 := by
  have he : (generalMeanRows 601).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 601) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 601)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0601

/-! Kernel-checked entropy margins for general spectral rectangle 602. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0602
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5090327027, 4920033252, 4757322243, 4601760539, 4452945367, 4310501960, 4174081173, 4043357336, 3918026341, 3797803906, 3682424018, 3571637524, 3465210846, 3362924824, 3264573654, 3169963923, 3078913728, 2991251867, 2906817096, 2825457454, 2747029634, 2671398406, 2598436088, 2528022052, 2460042275, 2394388914, 2330959921, 2269658680, 2210393671, 2153078161, 2097629915, 2043970921, 1992027147, 1941728297, 1893007602, 1845801609, 1800049995, 1755695383, 1712683182, 1670961423, 1630480622, 1591193632, 1553055525, 1516023461, 1480056584, 1445115909, 1411164223, 1378165995, 1346087281, 1314895648, 1284560087, 1255050949, 1226339866, 1198399693, 1171204440, 1144729219, 1118950186, 1093844488, 1069390217, 1045566362, 1022352766, 999730084, 977679742, 956183904, 935225435, 914787866, 894855368, 875412715, 856445261, 837938914, 819880106, 802255773, 785053333, 768260659, 751866065, 735858283, 720226445, 704960068, 690049033, 675483572, 661254254, 647351969, 633767913, 620493580, 607520745, 594841453, 582448013, 570332978, 558489145, 546909538, 535587404, 524516199, 513689585, 503101418, 492745745, 482616792, 472708958, 463016811, 453535082, 444258654, 435182562, 426301985, 417612238, 409108774, 400787174, 392643141, 384672502, 376871197, 369235280, 361760912, 354444360, 347281989, 340270265, 333405747, 326685084, 320105015, 313662363, 307354037, 301177020, 295128379, 289205251]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 602).prefactor = (4702344227453507/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 602).cutoff/(generalMeanRows 602).c)).2 =
    (9737753075837/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 602).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 602).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 602).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 602

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 602).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 602).criticalRate j.val*(generalMeanRows 602).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 602).c*(generalMeanRows 602).criticalPoint j.val)).2-
      (generalMeanRows 602).J/2-(generalMeanRows 602).error (generalMeanGrid j.val)+
      (generalMeanRows 602).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 602).c)).2-
      (generalMeanRows 602).J/2-(generalMeanRows 602).error 4 := by
  have he : (generalMeanRows 602).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 602) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 602)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0602

/-! Kernel-checked entropy margins for general spectral rectangle 603. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0603
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5015972121, 4845798846, 4683224576, 4527815742, 4379169420, 4236910658, 4100690088, 3970181790, 3845081379, 3725104271, 3609984136, 3499471478, 3393332370, 3291347283, 3193310037, 3099026834, 3008315376, 2921004062, 2836931248, 2755944566, 2677900302, 2602662819, 2530104027, 2460102895, 2392544995, 2327322085, 2264331720, 2203476893, 2144665697, 2087811017, 2032830241, 1979644989, 1928180863, 1878367213, 1830136919, 1783426186, 1738174355, 1694323722, 1651819375, 1610609035, 1570642910, 1531873558, 1494255761, 1457746398, 1422304340, 1387890335, 1354466914, 1321998293, 1290450288, 1259790228, 1229986878, 1201010368, 1172832117, 1145424774, 1118762149, 1092819164, 1067571787, 1042996988, 1019072687, 995777708, 973091733, 950995263, 929469580, 908496705, 888059367, 868140970, 848725556, 829797783, 811342892, 793346680, 775795476, 758676119, 741975929, 725682693, 709784639, 694270418, 679129086, 664350085, 649923230, 635838689, 622086968, 608658900, 595545628, 582738596, 570229530, 558010434, 546073573, 534411466, 523016872, 511882784, 501002419, 490369208, 479976787, 469818992, 459889849, 450183566, 440694530, 431417295, 422346580, 413477261, 404804365, 396323065, 388028675, 379916645, 371982556, 364222113, 356631145, 349205598, 341941531, 334835112, 327882616, 321080419, 314424997, 307912921, 301540853, 295305547, 289203840, 283232656, 277388997, 271669945, 266072658]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 603).prefactor = (9407724013679/2000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 603).cutoff/(generalMeanRows 603).c)).2 =
    (190280848904929/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 603).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 603).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 603).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 603

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 603).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 603).criticalRate j.val*(generalMeanRows 603).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 603).c*(generalMeanRows 603).criticalPoint j.val)).2-
      (generalMeanRows 603).J/2-(generalMeanRows 603).error (generalMeanGrid j.val)+
      (generalMeanRows 603).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 603).c)).2-
      (generalMeanRows 603).J/2-(generalMeanRows 603).error 4 := by
  have he : (generalMeanRows 603).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 603) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 603)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0603

/-! Kernel-checked entropy margins for general spectral rectangle 604. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0604
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5024627797, 4854160867, 4691306055, 4535629044, 4386726215, 4244221968, 4107766332, 3977032827, 3851716539, 3731532396, 3616213607, 3505510246, 3399187982, 3297026907, 3198820486, 3104374585, 3013506593, 2926044613, 2841826721, 2760700287, 2682521348, 2607154033, 2534470032, 2464348105, 2396673625, 2331338165, 2268239103, 2207279263, 2148366581, 2091413791, 2036338139, 1983061109, 1931508176, 1881608566, 1833295045, 1786503707, 1741173789, 1697247486, 1654669793, 1613388339, 1573353247, 1534516994, 1496834282, 1460261919, 1424758701, 1390285310, 1356804213, 1324279563, 1292677118, 1261964150, 1232109372, 1203082859, 1174855983, 1147401345, 1120692711, 1094704957, 1069414013, 1044796807, 1020831222, 997496044, 974770922, 952636322, 931073494, 910064428, 889591823, 869639053, 850190136, 831229701, 812742964, 794715697, 777134206, 759985307, 743256300, 726934948, 711009460, 695468467, 680301006, 665496503, 651044753, 636935906, 623160455, 609709215, 596573315, 583744183, 571213531, 558973350, 547015890, 535333658, 523919402, 512766101, 501866960, 491215400, 480805046, 470629722, 460683445, 450960413, 441455003, 432161759, 423075391, 414190767, 405502904, 397006969, 388698266, 380572238, 372624457, 364850623, 357246556, 349808195, 342531593, 335412911, 328448417, 321634483, 314967576, 308444262, 302061199, 295815133, 289702897, 283721408, 277867666, 272138745, 266531799]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 604).prefactor = (942395819706823/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 604).cutoff/(generalMeanRows 604).c)).2 =
    (190280848904929/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 604).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 604).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 604).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 604

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 604).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 604).criticalRate j.val*(generalMeanRows 604).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 604).c*(generalMeanRows 604).criticalPoint j.val)).2-
      (generalMeanRows 604).J/2-(generalMeanRows 604).error (generalMeanGrid j.val)+
      (generalMeanRows 604).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 604).c)).2-
      (generalMeanRows 604).J/2-(generalMeanRows 604).error 4 := by
  have he : (generalMeanRows 604).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 604) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 604)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0604

/-! Kernel-checked entropy margins for general spectral rectangle 605. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0605
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4958992684, 4788410984, 4625476207, 4469752327, 4320834104, 4178344408, 4041931811, 3911268451, 3786048099, 3665984430, 3550809459, 3440272123, 3334137000, 3232183145, 3134203026, 3040001559, 2949395220, 2862211239, 2778286855, 2697468632, 2619611838, 2544579861, 2472243681, 2402481372, 2335177653, 2270223465, 2207515579, 2146956236, 2088452811, 2031917498, 1977267023, 1924422371, 1873308536, 1823854283, 1775991930, 1729657144, 1684788749, 1641328546, 1599221145, 1558413810, 1518856311, 1480500783, 1443301604, 1407215265, 1372200263, 1338216987, 1305227626, 1273196065, 1242087803, 1211869866, 1182510728, 1153980237, 1126249546, 1099291045, 1073078300, 1047585994, 1022789870, 998666681, 975194138, 952350867, 930116360, 908470936, 887395702, 866872512, 846883938, 827413229, 808444284, 789961623, 771950353, 754396147, 737285213, 720604276, 704340549, 688481714, 673015901, 657931669, 643217986, 628864211, 614860078, 601195681, 587861457, 574848171, 562146905, 549749042, 537646256, 525830497, 514293982, 503029184, 492028823, 481285851, 470793449, 460545016, 450534156, 440754678, 431200582, 421866055, 412745460, 403833335, 395124382, 386613463, 378295592, 370165932, 362219789, 354452606, 346859957, 339437547, 332181201, 325086864, 318150598, 311368572, 304737065, 298252459, 291911234, 285709970, 279645337, 273714098, 267913102, 262239283, 256689656, 251261316, 245951436]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 605).prefactor = (189130213088423/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 605).cutoff/(generalMeanRows 605).c)).2 =
    (93274744152067/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 605).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 605).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 605).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 605

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 605).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 605).criticalRate j.val*(generalMeanRows 605).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 605).c*(generalMeanRows 605).criticalPoint j.val)).2-
      (generalMeanRows 605).J/2-(generalMeanRows 605).error (generalMeanGrid j.val)+
      (generalMeanRows 605).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 605).c)).2-
      (generalMeanRows 605).J/2-(generalMeanRows 605).error 4 := by
  have he : (generalMeanRows 605).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 605) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 605)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0605

/-! Kernel-checked entropy margins for general spectral rectangle 606. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0606
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4911547204, 4740293245, 4576747164, 4420469679, 4271052504, 4128115638, 3991304959, 3860290060, 3734762318, 3614433144, 3499032412, 3388307034, 3282019671, 3179947558, 3081881440, 2987624591, 2896991933, 2809809214, 2725912265, 2645146309, 2567365335, 2492431514, 2420214663, 2350591750, 2283446436, 2218668651, 2156154202, 2095804409, 2037525764, 1981229620, 1926831898, 1874252811, 1823416616, 1774251371, 1726688721, 1680663686, 1636114469, 1592982278, 1551211157, 1510747826, 1471541532, 1433543914, 1396708869, 1360992431, 1326352659, 1292749523, 1260144806, 1228502011, 1197786266, 1167964244, 1139004080, 1110875298, 1083548741, 1056996501, 1031191860, 1006109228, 981724090, 958012948, 934953277, 912523473, 890702812, 869471405, 848810159, 828700741, 809125540, 790067634, 771510757, 753439272, 735838136, 718692881, 701989579, 685714826, 669855712, 654399804, 639335122, 624650118, 610333662, 596375020, 582763836, 569490121, 556544231, 543916858, 531599013, 519582013, 507857469, 496417273, 485253589, 474358838, 463725691, 453347058, 443216078, 433326112, 423670730, 414243709, 405039019, 396050819, 387273451, 378701429, 370329436, 362152316, 354165070, 346362847, 338740942, 331294788, 324019954, 316912136, 309967159, 303180963, 296549610, 290069271, 283736225, 277546859, 271497657, 265585205, 259806182, 254157357, 248635588, 243237821, 237961082, 232802479, 227759195]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 606).prefactor = (2380488321979003/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 606).cutoff/(generalMeanRows 606).c)).2 =
    (182845767665203/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 606).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 606).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 606).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 606

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 606).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 606).criticalRate j.val*(generalMeanRows 606).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 606).c*(generalMeanRows 606).criticalPoint j.val)).2-
      (generalMeanRows 606).J/2-(generalMeanRows 606).error (generalMeanGrid j.val)+
      (generalMeanRows 606).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 606).c)).2-
      (generalMeanRows 606).J/2-(generalMeanRows 606).error 4 := by
  have he : (generalMeanRows 606).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 606) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 606)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0606

/-! Kernel-checked entropy margins for general spectral rectangle 607. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0607
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4897875237, 4727157219, 4564108854, 4408294011, 4259307288, 4116771333, 3980334452, 3849668465, 3724466794, 3604442724, 3489327853, 3378870673, 3272835295, 3171000286, 3073157613, 2979111675, 2888678419, 2801684541, 2717966736, 2637371023, 2559752119, 2484972864, 2412903687, 2343422115, 2276412323, 2211764710, 2149375515, 2089146448, 2030984362, 1974800938, 1920512395, 1868039220, 1817305918, 1768240777, 1720775644, 1674845729, 1630389406, 1587348038, 1545665809, 1505289565, 1466168672, 1428254870, 1391502153, 1355866639, 1321306462, 1287781663, 1255254088, 1223687294, 1193046460, 1163298302, 1134410998, 1106354106, 1079098500, 1052616303, 1026880820, 1001866485, 977548801, 953904289, 930910439, 908545662, 886789244, 865621307, 845022770, 824975306, 805461311, 786463871, 767966725, 749954241, 732411382, 715323681, 698677218, 682458591, 666654892, 651253693, 636243015, 621611314, 607347464, 593440731, 579880765, 566657578, 553761530, 541183315, 528913948, 516944748, 505267330, 493873591, 482755695, 471906070, 461317390, 450982569, 440894750, 431047298, 421433788, 412048001, 402883913, 393935686, 385197669, 376664379, 368330506, 360190899, 352240564, 344474655, 336888475, 329477461, 322237188, 315163359, 308251803, 301498469, 294899423, 288450843, 282149015, 275990330, 269971282, 264088460, 258338551, 252718331, 247224665, 241854503, 236604880, 231472908, 226455780]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 607).prefactor = (236575744042127/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 607).cutoff/(generalMeanRows 607).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 607).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 607).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 607).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 607

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 607).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 607).criticalRate j.val*(generalMeanRows 607).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 607).c*(generalMeanRows 607).criticalPoint j.val)).2-
      (generalMeanRows 607).J/2-(generalMeanRows 607).error (generalMeanGrid j.val)+
      (generalMeanRows 607).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 607).c)).2-
      (generalMeanRows 607).J/2-(generalMeanRows 607).error 4 := by
  have he : (generalMeanRows 607).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 607) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 607)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0607

/-! Kernel-checked entropy margins for general spectral rectangle 608. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0608
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4969084002, 4798180515, 4634931356, 4478900563, 4329682940, 4186901371, 4050204430, 3919264230, 3793774505, 3673448877, 3558019292, 3447234606, 3340859309, 3238672355, 3140466103, 3046045353, 2955226460, 2867836526, 2783712659, 2702701288, 2624657542, 2549444669, 2476933505, 2407001984, 2339534680, 2274422388, 2211561737, 2150854824, 2092208881, 2035535962, 1980752651, 1927779797, 1876542255, 1826968658, 1778991190, 1732545388, 1687569950, 1644006550, 1601799676, 1560896473, 1521246592, 1482802057, 1445517130, 1409348195, 1374253642, 1340193758, 1307130630, 1275028046, 1243851410, 1213567654, 1184145164, 1155553699, 1127764329, 1100749361, 1074482283, 1048937698, 1024091277, 999919700, 976400609, 953512562, 931234984, 909548133, 888433053, 867871541, 847846110, 828339955, 809336923, 790821480, 772778686, 755194164, 738054079, 721345109, 705054424, 689169667, 673678927, 658570724, 643833990, 629458047, 615432598, 601747701, 588393762, 575361516, 562642016, 550226616, 538106962, 526274979, 514722859, 503443050, 492428249, 481671386, 471165620, 460904328, 450881097, 441089715, 431524164, 422178613, 413047409, 404125073, 395406292, 386885911, 378558931, 370420502, 362465916, 354690602, 347090123, 339660172, 332396562, 325295228, 318352221, 311563700, 304925934, 298435297, 292088259, 285881392, 279811358, 273874911, 268068894, 262390232, 256835935, 251403090, 246088863]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 608).prefactor = (189195348542361/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 608).cutoff/(generalMeanRows 608).c)).2 =
    (371671424617083/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 608).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 608).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 608).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 608

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 608).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 608).criticalRate j.val*(generalMeanRows 608).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 608).c*(generalMeanRows 608).criticalPoint j.val)).2-
      (generalMeanRows 608).J/2-(generalMeanRows 608).error (generalMeanGrid j.val)+
      (generalMeanRows 608).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 608).c)).2-
      (generalMeanRows 608).J/2-(generalMeanRows 608).error 4 := by
  have he : (generalMeanRows 608).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 608) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 608)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0608

/-! Kernel-checked entropy margins for general spectral rectangle 609. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0609
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4977694154, 4806494535, 4642962507, 4486661353, 4337185173, 4194156201, 4057222399, 3926055313, 3800348147, 3679814025, 3564184429, 3453207783, 3346648164, 3244284146, 3145907728, 3051323371, 2960347112, 2872805754, 2788536121, 2707384378, 2629205402, 2553862205, 2481225398, 2411172703, 2343588495, 2278363381, 2215393808, 2154581706, 2095834144, 2039063025, 1984184789, 1931120147, 1879793823, 1830134327, 1782073727, 1735547447, 1690494077, 1646855193, 1604575186, 1563601108, 1523882524, 1485371374, 1448021841, 1411790235, 1376634872, 1342515972, 1309395553, 1277237344, 1246006686, 1215670457, 1186196984, 1157555978, 1129718456, 1102656679, 1076344086, 1050755239, 1025865765, 1001652305, 978092462, 955164755, 932848576, 911124147, 889972480, 869375340, 849315210, 829775256, 810739297, 792191771, 774117714, 756502723, 739332938, 722595015, 706276103, 690363822, 674846240, 659711859, 644949589, 630548737, 616498985, 602790376, 589413298, 576358471, 563616931, 551180018, 539039364, 527186879, 515614742, 504315388, 493281501, 482505999, 471982029, 461702957, 451662359, 441854011, 432271885, 422910141, 413763115, 404825319, 396091430, 387556285, 379214877, 371062346, 363093976, 355305190, 347691542, 340248716, 332972520, 325858882, 318903844, 312103560, 305454293, 298952409, 292594374, 286376751, 280296199, 274349466, 268533389, 262844887, 257280966, 251838707, 246515272]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 609).prefactor = (947615878560053/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 609).cutoff/(generalMeanRows 609).c)).2 =
    (371671424617083/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 609).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 609).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 609).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 609

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 609).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 609).criticalRate j.val*(generalMeanRows 609).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 609).c*(generalMeanRows 609).criticalPoint j.val)).2-
      (generalMeanRows 609).J/2-(generalMeanRows 609).error (generalMeanGrid j.val)+
      (generalMeanRows 609).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 609).c)).2-
      (generalMeanRows 609).J/2-(generalMeanRows 609).error 4 := by
  have he : (generalMeanRows 609).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 609) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 609)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0609

/-! Kernel-checked entropy margins for general spectral rectangle 610. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0610
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4906397131, 4735382079, 4572050023, 4415964075, 4266718128, 4123934172, 3987259902, 3856366567, 3730947055, 3610714154, 3495398992, 3384749626, 3278529755, 3176517562, 3078504651, 2984295081, 2893704479, 2806559239, 2722695771, 2641959828, 2564205875, 2489296510, 2417101938, 2347499474, 2280373090, 2215612997, 2153115249, 2092781389, 2034518106, 1978236927, 1923853926, 1871289452, 1820467879, 1771317368, 1723769650, 1677759821, 1633226147, 1590109891, 1548355138, 1507908644, 1468719683, 1430739915, 1393923250, 1358225734, 1323605425, 1290022296, 1257438126, 1225816408, 1195122261, 1165322345, 1136384778, 1108279070, 1080976042, 1054447767, 1028667507, 1003609649, 979249654, 955564003, 932530146, 910126455, 888332183, 867127416, 846493039, 826410694, 806862746, 787832252, 769302923, 751259099, 733685716, 716568285, 699892859, 683646012, 667814816, 652386820, 637350024, 622692866, 608404198, 594473269, 580889710, 567643515, 554725029, 542124929, 529834214, 517844189, 506146453, 494732889, 483595650, 472727148, 462120044, 451767241, 441661870, 431797284, 422167048, 412764930, 403584897, 394621102, 385867880, 377319744, 368971370, 360817601, 352853433, 345074013, 337474632, 330050724, 322797854, 315711717, 308788136, 302023052, 295412524, 288952723, 282639930, 276470530, 270441009, 264547952, 258788039, 253158040, 247654815, 242275310, 237016553, 231875652, 226849795]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 610).prefactor = (4739747322263501/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 610).cutoff/(generalMeanRows 610).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 610).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 610).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 610).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 610

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 610).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 610).criticalRate j.val*(generalMeanRows 610).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 610).c*(generalMeanRows 610).criticalPoint j.val)).2-
      (generalMeanRows 610).J/2-(generalMeanRows 610).error (generalMeanGrid j.val)+
      (generalMeanRows 610).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 610).c)).2-
      (generalMeanRows 610).J/2-(generalMeanRows 610).error 4 := by
  have he : (generalMeanRows 610).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 610) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 610)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0610

/-! Kernel-checked entropy margins for general spectral rectangle 611. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0611
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4914933853, 4743621249, 4580005009, 4423647484, 4274141862, 4131109474, 3994197401, 3863076324, 3737438592, 3616996496, 3501480695, 3390638808, 3284234123, 3182044438, 3083860993, 2989487505, 2898739284, 2811442418, 2727433035, 2646556618, 2568667379, 2493627678, 2421307494, 2351583927, 2284340749, 2219467978, 2156861490, 2096422654, 2038057997, 1981678894, 1927201271, 1874545340, 1823635341, 1774399313, 1726768866, 1680678983, 1636067825, 1592876550, 1551049147, 1510532279, 1471275133, 1433229283, 1396348561, 1360588933, 1325908388, 1292266827, 1259625963, 1227949226, 1197201674, 1167349908, 1138361993, 1110207383, 1082856850, 1056282419, 1030457303, 1005355846, 980953467, 957226605, 934152671, 911710000, 889877807, 868636146, 847965866, 827848579, 808266620, 789203015, 770641446, 752566227, 734962268, 717815054, 701110614, 684835499, 668976758, 653521918, 638458960, 623776300, 609462770, 595507603, 581900409, 568631167, 555690204, 543068181, 530756081, 518745194, 507027106, 495593683, 484437066, 473549653, 462924094, 452553279, 442430325, 432548576, 422901584, 413483107, 404287101, 395307709, 386539258, 377976249, 369613350, 361445394, 353467368, 345674413, 338061810, 330624985, 323359495, 316261029, 309325401, 302548546, 295926517, 289455477, 283131700, 276951566, 270911554, 265008244, 259238308, 253598514, 248085714, 242696849, 237428942, 232279096, 227244494]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 611).prefactor = (4747994087446189/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 611).cutoff/(generalMeanRows 611).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 611).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 611).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 611).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 611

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 611).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 611).criticalRate j.val*(generalMeanRows 611).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 611).c*(generalMeanRows 611).criticalPoint j.val)).2-
      (generalMeanRows 611).J/2-(generalMeanRows 611).error (generalMeanGrid j.val)+
      (generalMeanRows 611).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 611).c)).2-
      (generalMeanRows 611).J/2-(generalMeanRows 611).error 4 := by
  have he : (generalMeanRows 611).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 611) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 611)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0611

/-! Kernel-checked entropy margins for general spectral rectangle 612. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0612
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5214004871, 5046909798, 4887174316, 4734376198, 4588123228, 4448050578, 4313818467, 4185110065, 4061629615, 3943100739, 3829264912, 3719880078, 3614719396, 3513570105, 3416232486, 3322518913, 3232252995, 3145268780, 3061410032, 2980529563, 2902488623, 2827156333, 2754409169, 2684130475, 2616210026, 2550543613, 2487032661, 2425583883, 2366108942, 2308524155, 2252750208, 2198711888, 2146337842, 2095560347, 2046315096, 1998541000, 1952179998, 1907176889, 1863479161, 1821036848, 1779802379, 1739730450, 1700777893, 1662903565, 1626068233, 1590234469, 1555366559, 1521430404, 1488393439, 1456224551, 1424894000, 1394373351, 1364635406, 1335654137, 1307404629, 1279863023, 1253006464, 1226813046, 1201261769, 1176332494, 1152005898, 1128263436, 1105087301, 1082460393, 1060366279, 1038789166, 1017713869, 997125781, 977010847, 957355541, 938146837, 919372190, 901019509, 883077144, 865533859, 848378819, 831601568, 815192015, 799140416, 783437363, 768073763, 753040832, 738330075, 723933279, 709842499, 696050046, 682548480, 669330594, 656389411, 643718170, 631310320, 619159511, 607259585, 595604570, 584188673, 573006271, 562051908, 551320283, 540806253, 530504818, 520411121, 510520442, 500828192, 491329911, 482021257, 472898011, 463956065, 455191422, 446600191, 438178584, 429922912, 421829581, 413895091, 406116031, 398489078, 391010991, 383678610, 376488857, 369438726, 362525288, 355745683]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 612).prefactor = (1152508401404431/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 612).cutoff/(generalMeanRows 612).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 612).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 612).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 612).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 612

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 612).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 612).criticalRate j.val*(generalMeanRows 612).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 612).c*(generalMeanRows 612).criticalPoint j.val)).2-
      (generalMeanRows 612).J/2-(generalMeanRows 612).error (generalMeanGrid j.val)+
      (generalMeanRows 612).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 612).c)).2-
      (generalMeanRows 612).J/2-(generalMeanRows 612).error 4 := by
  have he : (generalMeanRows 612).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 612) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 612)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0612

/-! Kernel-checked entropy margins for general spectral rectangle 613. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0613
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5231679241, 5064017752, 4903740800, 4750424728, 4603675992, 4463128526, 4328441396, 4199296700, 4075397677, 3956467014, 3842245308, 3732489682, 3626972528, 3525480362, 3427812789, 3333781547, 3243209647, 3155930574, 3071787562, 2990632925, 2912327443, 2836739793, 2763746031, 2693229108, 2625078423, 2559189414, 2495463175, 2433806097, 2374129549, 2316349562, 2260386553, 2206165054, 2153613471, 2102663852, 2053251670, 2005315630, 1958797474, 1913641814, 1869795960, 1827209777, 1785835532, 1745627767, 1706543169, 1668540456, 1631580259, 1595625027, 1560638922, 1526587730, 1493438777, 1461160843, 1429724088, 1399099981, 1369261230, 1340181721, 1311836453, 1284201487, 1257253890, 1230971682, 1205333792, 1180320012, 1155910954, 1132088010, 1108833313, 1086129704, 1063960696, 1042310441, 1021163703, 1000505825, 980322707, 960600773, 941326956, 922488666, 904073774, 886070588, 868467835, 851254643, 834420521, 817955343, 801849333, 786093049, 770677370, 755593480, 740832857, 726387259, 712248714, 698409508, 684862174, 671599483, 658614432, 645900238, 633450328, 621258330, 609318066, 597623543, 586168949, 574948641, 563957144, 553189142, 542639471, 532303116, 522175204, 512250998, 502525894, 492995415, 483655207, 474501035, 465528778, 456734425, 448114071, 439663917, 431380259, 423259494, 415298107, 407492679, 399839871, 392336435, 384979199, 377765074, 370691045, 363754172, 356951586]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 613).prefactor = (2312830320699387/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 613).cutoff/(generalMeanRows 613).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 613).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 613).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 613).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 613

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 613).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 613).criticalRate j.val*(generalMeanRows 613).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 613).c*(generalMeanRows 613).criticalPoint j.val)).2-
      (generalMeanRows 613).J/2-(generalMeanRows 613).error (generalMeanGrid j.val)+
      (generalMeanRows 613).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 613).c)).2-
      (generalMeanRows 613).J/2-(generalMeanRows 613).error 4 := by
  have he : (generalMeanRows 613).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 613) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 613)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0613

/-! Kernel-checked entropy margins for general spectral rectangle 614. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0614
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4932051882, 4760142620, 4595956528, 4439054432, 4289028102, 4145497552, 4008108634, 3876530880, 3750455570, 3629593990, 3513675864, 3402447930, 3295672653, 3193127055, 3094601651, 2999899473, 2908835188, 2821234280, 2736932304, 2655774206, 2577613690, 2502312636, 2429740570, 2359774166, 2292296790, 2227198076, 2164373538, 2103724202, 2045156269, 1988580805, 1933913445, 1881074120, 1829986809, 1780579298, 1732782961, 1686532554, 1641766021, 1598424317, 1556451235, 1515793252, 1476399379, 1438221021, 1401211848, 1365327675, 1330526342, 1296767613, 1264013065, 1232226002, 1201371361, 1171415625, 1142326749, 1114074080, 1086628289, 1059961303, 1034046242, 1008857360, 984369991, 960560492, 937406194, 914885358, 892977127, 871661484, 850919213, 830731861, 811081700, 791951699, 773325483, 755187310, 737522039, 720315104, 703552484, 687220685, 671306711, 655798044, 640682624, 625948826, 611585444, 597581673, 583927087, 570611630, 557625596, 544959612, 532604631, 520551912, 508793011, 497319767, 486124293, 475198961, 464536394, 454129458, 443971248, 434055082, 424374491, 414923211, 405695177, 396684511, 387885521, 379292687, 370900661, 362704257, 354698446, 346878348, 339239232, 331776506, 324485711, 317362522, 310402738, 303602281, 296957188, 290463610, 284117808, 277916149, 271855101, 265931230, 260141199, 254481762, 248949762, 243542128, 238255873, 233088092, 228035955]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 614).prefactor = (47645306888287/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 614).cutoff/(generalMeanRows 614).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 614).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 614).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 614).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 614

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 614).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 614).criticalRate j.val*(generalMeanRows 614).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 614).c*(generalMeanRows 614).criticalPoint j.val)).2-
      (generalMeanRows 614).J/2-(generalMeanRows 614).error (generalMeanGrid j.val)+
      (generalMeanRows 614).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 614).c)).2-
      (generalMeanRows 614).J/2-(generalMeanRows 614).error 4 := by
  have he : (generalMeanRows 614).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 614) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 614)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0614

/-! Kernel-checked entropy margins for general spectral rectangle 615. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0615
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![4949229531, 4776721533, 4611963604, 4454515039, 4303966189, 4159935742, 4022068318, 3890032296, 3763517883, 3642235360, 3525913507, 3414298182, 3307151021, 3204248272, 3105379717, 3010347705, 2918966256, 2831060245, 2746464657, 2665023897, 2586591159, 2511027842, 2438203018, 2367992930, 2300280540, 2234955096, 2171911749, 2111051180, 2052279263, 1995506755, 1940648996, 1887625639, 1836360398, 1786780807, 1738818002, 1692406511, 1647484063, 1603991406, 1561872138, 1521072549, 1481541472, 1443230144, 1406092073, 1370082921, 1335160380, 1301284073, 1268415446, 1236517673, 1205555570, 1175495502, 1146305314, 1117954245, 1090412864, 1063653000, 1037647681, 1012371070, 987798415, 963905990, 940671049, 918071777, 896087242, 874697360, 853882846, 833625184, 813906585, 794709956, 776018868, 757817522, 740090726, 722823861, 706002860, 689614179, 673644779, 658082097, 642914032, 628128918, 613715511, 599662966, 585960824, 572598991, 559567728, 546857630, 534459618, 522364921, 510565066, 499051863, 487817396, 476854012, 466154310, 455711128, 445517538, 435566835, 425852528, 416368331, 407108156, 398066108, 389236472, 380613711, 372192457, 363967506, 355933811, 348086477, 340420755, 332932037, 325615849, 318467851, 311483828, 304659685, 297991448, 291475254, 285107351, 278884093, 272801935, 266857432, 261047235, 255368086, 249816819, 244390351, 239085685, 233899905, 228830173]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 615).prefactor = (478112488488809/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 615).cutoff/(generalMeanRows 615).c)).2 =
    (90709616587/250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 615).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 615).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 615).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 615

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 615).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 615).criticalRate j.val*(generalMeanRows 615).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 615).c*(generalMeanRows 615).criticalPoint j.val)).2-
      (generalMeanRows 615).J/2-(generalMeanRows 615).error (generalMeanGrid j.val)+
      (generalMeanRows 615).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 615).c)).2-
      (generalMeanRows 615).J/2-(generalMeanRows 615).error 4 := by
  have he : (generalMeanRows 615).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 615) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 615)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0615

/-! Kernel-checked entropy margins for general spectral rectangle 616. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0616
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5249413524, 5081183698, 4920363440, 4766527660, 4619281477, 4478257585, 4343113894, 4213531425, 4089212411, 3969878598, 3855269704, 3745142030, 3639267195, 3537430993, 3439432347, 3345082359, 3254203439, 3166628509, 3082200270, 3000770536, 2922199615, 2846355739, 2773114544, 2702358583, 2633976882, 2567864524, 2503922265, 2442056184, 2382177344, 2324201496, 2268048784, 2213643486, 2160913764, 2109791436, 2060211758, 2012113224, 1965437382, 1920128653, 1876134172, 1833403630, 1791889135, 1751545075, 1712327989, 1674196454, 1637110970, 1601033857, 1565929156, 1531762539, 1498501218, 1466113868, 1434570549, 1403842633, 1373902735, 1344724652, 1316283300, 1288554658, 1261515714, 1235144415, 1209419618, 1184321046, 1159829247, 1135925548, 1112592022, 1089811453, 1067567297, 1045843652, 1024625231, 1003897328, 983645793, 963857006, 944517855, 925615707, 907138392, 889074179, 871411757, 854140216, 837249030, 820728038, 804567432, 788757738, 773289803, 758154782, 743344123, 728849558, 714663086, 700776968, 687183712, 673876062, 660846995, 648089703, 635597590, 623364264, 611383525, 599649360, 588155937, 576897595, 565868839, 555064336, 544478904, 534107511, 523945267, 513987420, 504229350, 494666565, 485294696, 476109493, 467106822, 458282657, 449633083, 441154284, 432842547, 424694253, 416705880, 408873992, 401195244, 393666372, 386284197, 379045618, 371947609, 364987221, 358161576]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 616).prefactor = (580167581189429/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 616).cutoff/(generalMeanRows 616).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 616).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 616).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 616).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 616

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 616).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 616).criticalRate j.val*(generalMeanRows 616).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 616).c*(generalMeanRows 616).criticalPoint j.val)).2-
      (generalMeanRows 616).J/2-(generalMeanRows 616).error (generalMeanGrid j.val)+
      (generalMeanRows 616).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 616).c)).2-
      (generalMeanRows 616).J/2-(generalMeanRows 616).error 4 := by
  have he : (generalMeanRows 616).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 616) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 616)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0616

/-! Kernel-checked entropy margins for general spectral rectangle 617. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0617
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5267207922, 5098407832, 4937042429, 4782685178, 4634939861, 4493437928, 4357836129, 4227814402, 4103073973, 3983335644, 3868338251, 3757837267, 3651603539, 3549422133, 3451091293, 3356421479, 3265234499, 3177362708, 3092648275, 3010942512, 2932105252, 2856004281, 2782514814, 2711519005, 2642905505, 2576569039, 2512410030, 2450334236, 2390252420, 2332080046, 2275736988, 2221147267, 2168238803, 2116943181, 2067195438, 2018933861, 1972099798, 1926637482, 1882493869, 1839618479, 1797963259, 1757482441, 1718132417, 1679871625, 1642660429, 1606461022, 1571237324, 1536954889, 1503580819, 1471083683, 1439433439, 1408601362, 1378559974, 1349282984, 1320745221, 1292922585, 1265791984, 1239331292, 1213519294, 1188335643, 1163760822, 1139776094, 1116363473, 1093505683, 1071186123, 1049388840, 1028098493, 1007300327, 986980143, 967124277, 947719570, 928753348, 910213399, 892087952, 874365658, 857035570, 840087126, 823510132, 807294745, 791431459, 775911091, 760724766, 745863902, 731320203, 717085643, 703152454, 689513119, 676160359, 663087126, 650286589, 637752131, 625477337, 613455986, 601682045, 590149661, 578853155, 567787015, 556945886, 546324572, 535918022, 525721330, 515729728, 505938580, 496343379, 486939742, 477723403, 468690215, 459836138, 451157244, 442649703, 434309791, 426133877, 418118424, 410259988, 402555210, 395000818, 387593619, 380330502, 373208432, 366224450, 359375668]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 617).prefactor = (465707380953267/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 617).cutoff/(generalMeanRows 617).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 617).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 617).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 617).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 617

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 617).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 617).criticalRate j.val*(generalMeanRows 617).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 617).c*(generalMeanRows 617).criticalPoint j.val)).2-
      (generalMeanRows 617).J/2-(generalMeanRows 617).error (generalMeanGrid j.val)+
      (generalMeanRows 617).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 617).c)).2-
      (generalMeanRows 617).J/2-(generalMeanRows 617).error 4 := by
  have he : (generalMeanRows 617).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 617) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 617)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0617

/-! Kernel-checked entropy margins for general spectral rectangle 618. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0618
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5027866391, 4854915542, 4689717821, 4531831147, 4380844652, 4236375966, 4098068782, 3965590684, 3838631191, 3716900000, 3600125404, 3488052854, 3380443658, 3277073801, 3177732871, 3082223073, 2990358335, 2901963486, 2816873505, 2734932826, 2655994707, 2579920637, 2506579805, 2435848591, 2367610115, 2301753801, 2238174987, 2176774557, 2117458598, 2060138086, 2004728590, 1951149998, 1899326260, 1849185154, 1800658058, 1753679745, 1708188188, 1664124382, 1621432166, 1580058072, 1539951172, 1501062939, 1463347113, 1426759584, 1391258270, 1356803013, 1323355474, 1290879038, 1259338724, 1228701101, 1198934204, 1170007463, 1141891630, 1114558712, 1087981908, 1062135548, 1036995039, 1012536811, 988738267, 965577734, 943034420, 921088370, 899720429, 878912200, 858646011, 838904880, 819672483, 800933122, 782671700, 764873690, 747525108, 730612496, 714122887, 698043795, 682363183, 667069451, 652151415, 637598285, 623399653, 609545476, 596026058, 582832035, 569954366, 557384314, 545113436, 533133572, 521436830, 510015580, 498862438, 487970261, 477332134, 466941364, 456791467, 446876165, 437189376, 427725204, 418477937, 409442035, 400612126, 391983001, 383549606, 375307037, 367250532, 359375473, 351677373, 344151876, 336794749, 329601882, 322569280, 315693061, 308969451, 302394782, 295965487, 289678095, 283529233, 277515617, 271634053, 265881432, 260254728, 254750996, 249367369]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 618).prefactor = (958784880920799/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 618).cutoff/(generalMeanRows 618).c)).2 =
    (93274744152067/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 618).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 618).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 618).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 618

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 618).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 618).criticalRate j.val*(generalMeanRows 618).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 618).c*(generalMeanRows 618).criticalPoint j.val)).2-
      (generalMeanRows 618).J/2-(generalMeanRows 618).error (generalMeanGrid j.val)+
      (generalMeanRows 618).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 618).c)).2-
      (generalMeanRows 618).J/2-(generalMeanRows 618).error 4 := by
  have he : (generalMeanRows 618).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 618) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 618)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0618

/-! Kernel-checked entropy margins for general spectral rectangle 619. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0619
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5233984799, 5058902058, 4891608202, 4731658490, 4578639650, 4432167125, 4291882626, 4157451938, 4028562950, 3904923884, 3786261695, 3672320623, 3562860885, 3457657478, 3356499101, 3259187156, 3165534853, 3075366378, 2988516129, 2904828029, 2824154876, 2746357754, 2671305492, 2598874159, 2528946596, 2461411988, 2396165469, 2333107744, 2272144752, 2213187343, 2156150984, 2100955479, 2047524717, 1995786424, 1945671945, 1897116035, 1850056656, 1804434804, 1760194331, 1717281785, 1675646264, 1635239271, 1596014584, 1557928133, 1520937880, 1485003715, 1450087346, 1416152212, 1383163382, 1351087478, 1319892590, 1289548199, 1260025110, 1231295382, 1203332264, 1176110137, 1149604455, 1123791693, 1098649299, 1074155643, 1050289970, 1027032365, 1004363707, 982265631, 960720494, 939711341, 919221873, 899236413, 879739882, 860717768, 842156103, 824041433, 806360804, 789101729, 772252175, 755800541, 739735635, 724046664, 708723209, 693755213, 679132965, 664847084, 650888508, 637248477, 623918525, 610890461, 598156365, 585708573, 573539668, 561642470, 550010025, 538635598, 527512664, 516634901, 505996177, 495590552, 485412260, 475455711, 465715480, 456186303, 446863069, 437740816, 428814725, 420080115, 411532438, 403167275, 394980330, 386967426, 379124504, 371447614, 363932913, 356576665, 349375233, 342325076, 335422748, 328664895, 322048249, 315569629, 309225935, 303014147, 296931323]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 619).prefactor = (4827100176226049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 619).cutoff/(generalMeanRows 619).c)).2 =
    (77616106044777/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 619).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 619).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 619).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 619

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 619).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 619).criticalRate j.val*(generalMeanRows 619).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 619).c*(generalMeanRows 619).criticalPoint j.val)).2-
      (generalMeanRows 619).J/2-(generalMeanRows 619).error (generalMeanGrid j.val)+
      (generalMeanRows 619).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 619).c)).2-
      (generalMeanRows 619).J/2-(generalMeanRows 619).error 4 := by
  have he : (generalMeanRows 619).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 619) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 619)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0619

/-! Kernel-checked entropy margins for general spectral rectangle 620. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0620
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5214258259, 5044649154, 4882535750, 4727488489, 4579108316, 4437024009, 4300889808, 4170383280, 4045203411, 3925068888, 3809716543, 3698899952, 3592388159, 3489964521, 3391425655, 3296580473, 3205249312, 3117263121, 3032462731, 2950698176, 2871828068, 2795719027, 2722245151, 2651287530, 2582733789, 2516477679, 2452418681, 2390461656, 2330516505, 2272497864, 2216324813, 2161920611, 2109212445, 2058131197, 2008611226, 1960590171, 1914008754, 1868810606, 1824942106, 1782352218, 1740992351, 1700816223, 1661779731, 1623840832, 1586959434, 1551097285, 1516217877, 1482286356, 1449269427, 1417135277, 1385853499, 1355395011, 1325731998, 1296837838, 1268687045, 1241255214, 1214518961, 1188455876, 1163044471, 1138264140, 1114095111, 1090518406, 1067515803, 1045069801, 1023163585, 1001780990, 980906476, 960525095, 940622462, 921184733, 902198580, 883651162, 865530109, 847823497, 830519831, 813608024, 797077379, 780917571, 765118634, 749670943, 734565201, 719792422, 705343922, 691211303, 677386442, 663861481, 650628815, 637681081, 625011151, 612612118, 600477291, 588600187, 576974519, 565594191, 554453290, 543546082, 532866998, 522410636, 512171749, 502145242, 492326165, 482709711, 473291205, 464066104, 455029992, 446178572, 437507667, 429013210, 420691247, 412537927, 404549502, 396722321, 389052831, 381537570, 374173165, 366956328, 359883858, 352952631, 346159605, 339501810, 332976354]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 620).prefactor = (937740061314861/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 620).cutoff/(generalMeanRows 620).c)).2 =
    (81074405466789/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 620).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 620).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 620).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 620

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 620).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 620).criticalRate j.val*(generalMeanRows 620).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 620).c*(generalMeanRows 620).criticalPoint j.val)).2-
      (generalMeanRows 620).J/2-(generalMeanRows 620).error (generalMeanGrid j.val)+
      (generalMeanRows 620).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 620).c)).2-
      (generalMeanRows 620).J/2-(generalMeanRows 620).error 4 := by
  have he : (generalMeanRows 620).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 620) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 620)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0620

/-! Kernel-checked entropy margins for general spectral rectangle 621. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0621
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5338990755, 5167890215, 5004325683, 4847864813, 4698105986, 4554675629, 4417225814, 4285432119, 4158991696, 4037621543, 3921056936, 3809050017, 3701368509, 3597794550, 3498123632, 3402163634, 3309733935, 3220664605, 3134795663, 3051976393, 2972064719, 2894926625, 2820435625, 2748472268, 2678923685, 2611683170, 2546649785, 2483728006, 2422827381, 2363862219, 2306751303, 2251417620, 2197788106, 2145793415, 2095367697, 2046448399, 1998976069, 1952894182, 1908148968, 1864689262, 1822466354, 1781433853, 1741547557, 1702765337, 1665047018, 1628354276, 1592650541, 1557900896, 1524071996, 1491131981, 1459050400, 1427798135, 1397347336, 1367671351, 1338744669, 1310542859, 1283042516, 1256221210, 1230057439, 1204530580, 1179620847, 1155309249, 1131577555, 1108408253, 1085784517, 1063690175, 1042109678, 1021028069, 1000430957, 980304490, 960635330, 941410632, 922618016, 904245551, 886281733, 868715466, 851536044, 834733135, 818296760, 802217286, 786485403, 771092114, 756028723, 741286819, 726858266, 712735192, 698909977, 685375242, 672123844, 659148858, 646443578, 634001499, 621816318, 609881919, 598192369, 586741912, 575524959, 564536085, 553770020, 543221648, 532885993, 522758223, 512833638, 503107672, 493575879, 484233938, 475077643, 466102901, 457305728, 448682245, 440228674, 431941336, 423816647, 415851115, 408041334, 400383988, 392875842, 385513741, 378294611, 371215449, 364273330]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 621).prefactor = (2360270790627219/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 621).cutoff/(generalMeanRows 621).c)).2 =
    (103236955285601/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 621).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 621).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 621).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 621

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 621).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 621).criticalRate j.val*(generalMeanRows 621).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 621).c*(generalMeanRows 621).criticalPoint j.val)).2-
      (generalMeanRows 621).J/2-(generalMeanRows 621).error (generalMeanGrid j.val)+
      (generalMeanRows 621).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 621).c)).2-
      (generalMeanRows 621).J/2-(generalMeanRows 621).error 4 := by
  have he : (generalMeanRows 621).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 621) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 621)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0621

/-! Kernel-checked entropy margins for general spectral rectangle 622. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0622
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5444252245, 5264996912, 5093712146, 4929941006, 4773258952, 4623271014, 4479609270, 4341930586, 4209914587, 4083261831, 3961692164, 3844943227, 3732769104, 3624939098, 3521236606, 3421458109, 3325412231, 3232918889, 3143808513, 3057921322, 2975106668, 2895222425, 2818134428, 2743715953, 2671847242, 2602415053, 2535312256, 2470437445, 2407694588, 2346992700, 2288245532, 2231371287, 2176292359, 2122935081, 2071229496, 2021109142, 1972510848, 1925374548, 1879643105, 1835262142, 1792179895, 1750347059, 1709716659, 1670243919, 1631886143, 1594602606, 1558354442, 1523104549, 1488817495, 1455459430, 1422998003, 1391402284, 1360642690, 1330690919, 1301519881, 1273103637, 1245417344, 1218437198, 1192140382, 1166505018, 1141510121, 1117135555, 1093361992, 1070170874, 1047544374, 1025465363, 1003917377, 982884584, 962351757, 942304245, 922727944, 903609276, 884935164, 866693006, 848870658, 831456412, 814438976, 797807455, 781551339, 765660478, 750125072, 734935657, 720083085, 705558516, 691353404, 677459484, 663868759, 650573491, 637566191, 624839608, 612386719, 600200719, 588275016, 576603220, 565179135, 553996752, 543050243, 532333953, 521842391, 511570232, 501512299, 491663570, 482019161, 472574330, 463324467, 454265090, 445391841, 436700483, 428186894, 419847062, 411677085, 403673163, 395831599, 388148790, 380621231, 373245504, 366018282, 358936322, 351996463, 345195625, 338530804]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 622).prefactor = (4926917449412447/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 622).cutoff/(generalMeanRows 622).c)).2 =
    (400003818084247/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 622).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 622).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 622).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 622

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 622).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 622).criticalRate j.val*(generalMeanRows 622).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 622).c*(generalMeanRows 622).criticalPoint j.val)).2-
      (generalMeanRows 622).J/2-(generalMeanRows 622).error (generalMeanGrid j.val)+
      (generalMeanRows 622).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 622).c)).2-
      (generalMeanRows 622).J/2-(generalMeanRows 622).error 4 := by
  have he : (generalMeanRows 622).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 622) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 622)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0622

/-! Kernel-checked entropy margins for general spectral rectangle 623. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0623
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5576065722, 5395187916, 5222325658, 5057018945, 4898840417, 4747392514, 4602304929, 4463232330, 4329852317, 4201863580, 4078984242, 3960950353, 3847514532, 3738444723, 3633523077, 3532544915, 3435317795, 3341660650, 3251402996, 3164384215, 3080452881, 2999466152, 2921289200, 2845794693, 2772862306, 2702378282, 2634235008, 2568330639, 2504568737, 2442857942, 2383111658, 2325247775, 2269188394, 2214859580, 2162191130, 2111116357, 2061571884, 2013497454, 1966835757, 1921532258, 1877535046, 1834794685, 1793264078, 1752898339, 1713654672, 1675492258, 1638372149, 1602257167, 1567111811, 1532902168, 1499595829, 1467161814, 1435570492, 1404793519, 1374803764, 1345575256, 1317083118, 1289303516, 1262213607, 1235791489, 1210016153, 1184867444, 1160326013, 1136373285, 1112991416, 1090163261, 1067872340, 1046102807, 1024839422, 1004067519, 983772981, 963942217, 944562136, 925620124, 907104022, 889002110, 871303082, 853996029, 837070426, 820516108, 804323261, 788482403, 772984373, 757820313, 742981659, 728460128, 714247705, 700336634, 686719406, 673388749, 660337618, 647559190, 635046848, 622794181, 610794968, 599043177, 587532956, 576258623, 565214664, 554395725, 543796604, 533412250, 523237752, 513268340, 503499373, 493926340, 484544855, 475350648, 466339566, 457507568, 448850717, 440365183, 432047234, 423893236, 415899650, 408063023, 400379995, 392847288, 385461706, 378220134, 371119533]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 623).prefactor = (4961076807755029/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 623).cutoff/(generalMeanRows 623).c)).2 =
    (81551158977713/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 623).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 623).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 623).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 623

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 623).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 623).criticalRate j.val*(generalMeanRows 623).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 623).c*(generalMeanRows 623).criticalPoint j.val)).2-
      (generalMeanRows 623).J/2-(generalMeanRows 623).error (generalMeanGrid j.val)+
      (generalMeanRows 623).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 623).c)).2-
      (generalMeanRows 623).J/2-(generalMeanRows 623).error 4 := by
  have he : (generalMeanRows 623).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 623) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 623)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0623

/-! Kernel-checked entropy margins for general spectral rectangle 624. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0624
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5258158704, 5077549298, 4905029393, 4740138454, 4582448423, 4431560886, 4287104544, 4148732952, 4016122487, 3888970524, 3766993783, 3649926840, 3537520775, 3429541944, 3325770859, 3226001169, 3130038729, 3037700744, 2948814986, 2863219079, 2780759836, 2701292647, 2624680923, 2550795572, 2479514522, 2410722277, 2344309506, 2280172659, 2218213615, 2158339350, 2100461633, 2044496741, 1990365187, 1937991481, 1887303891, 1838234229, 1790717651, 1744692463, 1700099950, 1656884204, 1614991973, 1574372514, 1534977454, 1496760665, 1459678143, 1423687892, 1388749819, 1354825636, 1321878761, 1289874235, 1258778634, 1228559990, 1199187721, 1170632558, 1142866478, 1115862643, 1089595344, 1064039939, 1039172807, 1014971294, 991413668, 968479075, 946147496, 924399707, 903217243, 882582362, 862478010, 842887791, 823795934, 805187269, 787047194, 769361654, 752117114, 735300537, 718899361, 702901478, 687295216, 672069319, 657212926, 642715559, 628567106, 614757802, 601278217, 588119242, 575272074, 562728207, 550479415, 538517745, 526835504, 515425249, 504279774, 493392108, 482755498, 472363406, 462209496, 452287631, 442591862, 433116423, 423855722, 414804338, 405957009, 397308632, 388854254, 380589068, 372508407, 364607739, 356882661, 349328898, 341942295, 334718814, 327654531, 320745632, 313988407, 307379248, 300914647, 294591190, 288405557, 282354516, 276434921, 270643709, 264977901]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 624).prefactor = (4970552786148247/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 624).cutoff/(generalMeanRows 624).c)).2 =
    (92834587270203/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 624).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 624).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 624).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 624

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 624).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 624).criticalRate j.val*(generalMeanRows 624).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 624).c*(generalMeanRows 624).criticalPoint j.val)).2-
      (generalMeanRows 624).J/2-(generalMeanRows 624).error (generalMeanGrid j.val)+
      (generalMeanRows 624).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 624).c)).2-
      (generalMeanRows 624).J/2-(generalMeanRows 624).error 4 := by
  have he : (generalMeanRows 624).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 624) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 624)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0624

/-! Kernel-checked entropy margins for general spectral rectangle 625. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0625
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5384188521, 5201807420, 5027564004, 4860994693, 4701668625, 4549184806, 4403169561, 4263274252, 4129173236, 4000562019, 3877155596, 3758686950, 3644905687, 3535576797, 3430479530, 3329406367, 3232162079, 3138562868, 3048435579, 2961616973, 2877953063, 2797298501, 2719516009, 2644475859, 2572055389, 2502138553, 2434615510, 2369382239, 2306340180, 2245395902, 2186460795, 2129450783, 2074286055, 2020890816, 1969193051, 1919124310, 1870619504, 1823616714, 1778057009, 1733884286, 1691045109, 1649488561, 1609166110, 1570031478, 1532040520, 1495151108, 1459323026, 1424517870, 1390698950, 1357831202, 1325881106, 1294816604, 1264607026, 1235223020, 1206636486, 1178820512, 1151749316, 1125398189, 1099743445, 1074762366, 1050433161, 1026734915, 1003647554, 981151798, 959229130, 937861753, 917032563, 896725114, 876923585, 857612756, 838777979, 820405150, 802480688, 784991508, 767925001, 751269015, 735011830, 719142144, 703649052, 688522029, 673750916, 659325904, 645237515, 631476595, 618034296, 604902064, 592071627, 579534986, 567284400, 555312379, 543611672, 532175257, 520996337, 510068323, 499384834, 488939683, 478726874, 468740590, 458975194, 449425212, 440085336, 430950414, 422015442, 413275565, 404726064, 396362360, 388179999, 380174656, 372342127, 364678324, 357179272, 349841107, 342660069, 335632501, 328754843, 322023633, 315435499, 308987159, 302675417, 296497163, 290449364]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 625).prefactor = (625698499909723/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 625).cutoff/(generalMeanRows 625).c)).2 =
    (378914142889271/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 625).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 625).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 625).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 625

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 625).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 625).criticalRate j.val*(generalMeanRows 625).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 625).c*(generalMeanRows 625).criticalPoint j.val)).2-
      (generalMeanRows 625).J/2-(generalMeanRows 625).error (generalMeanGrid j.val)+
      (generalMeanRows 625).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 625).c)).2-
      (generalMeanRows 625).J/2-(generalMeanRows 625).error 4 := by
  have he : (generalMeanRows 625).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 625) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 625)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0625

/-! Kernel-checked entropy margins for general spectral rectangle 626. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0626
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5504305011, 5315650561, 5135438113, 4963187707, 4798453191, 4640819274, 4489898890, 4345330845, 4206777708, 4073923905, 3946474005, 3824151169, 3706695741, 3593863976, 3485426870, 3381169103, 3280888067, 3184392980, 3091504071, 3002051832, 2915876331, 2832826578, 2752759939, 2675541602, 2601044069, 2529146704, 2459735295, 2392701664, 2327943296, 2265362994, 2204868561, 2146372503, 2089791755, 2035047416, 1982064512, 1930771772, 1881101411, 1832988943, 1786372984, 1741195089, 1697399588, 1654933429, 1613746041, 1573789198, 1535016893, 1497385220, 1460852262, 1425377989, 1390924158, 1357454219, 1324933229, 1293327772, 1262605878, 1232736949, 1203691695, 1175442065, 1147961186, 1121223307, 1095203740, 1069878814, 1045225819, 1021222966, 997849340, 975084858, 952910231, 931306927, 910257134, 889743728, 869750243, 850260836, 831260264, 812733854, 794667476, 777047524, 759860887, 743094932, 726737478, 710776781, 695201513, 680000745, 665163928, 650680880, 636541766, 622737091, 609257676, 596094655, 583239454, 570683784, 558419627, 546439228, 534735081, 523299921, 512126715, 501208652, 490539134, 480111769, 469920364, 459958913, 450221595, 440702765, 431396948, 422298830, 413403257, 404705225, 396199877, 387882497, 379748504, 371793449, 364013009, 356402982, 348959287, 341677955, 334555126, 327587047, 320770070, 314100642, 307575310, 301190711, 294943575, 288830714, 282849030]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 626).prefactor = (1289005599555631/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 626).cutoff/(generalMeanRows 626).c)).2 =
    (370332565742317/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 626).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 626).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 626).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 626

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 626).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 626).criticalRate j.val*(generalMeanRows 626).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 626).c*(generalMeanRows 626).criticalPoint j.val)).2-
      (generalMeanRows 626).J/2-(generalMeanRows 626).error (generalMeanGrid j.val)+
      (generalMeanRows 626).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 626).c)).2-
      (generalMeanRows 626).J/2-(generalMeanRows 626).error 4 := by
  have he : (generalMeanRows 626).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 626) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 626)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0626

/-! Kernel-checked entropy margins for general spectral rectangle 627. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0627
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5733018265, 5542024122, 5359514007, 5185004846, 5018047654, 4858224561, 4705146155, 4558449106, 4417794040, 4282863613, 4153360787, 4029007261, 3909542055, 3794720218, 3684311654, 3578100056, 3475881924, 3377465668, 3282670791, 3191327132, 3103274171, 3018360395, 2936442702, 2857385862, 2781062008, 2707350176, 2636135871, 2567310663, 2500771819, 2436421956, 2374168718, 2313924476, 2255606053, 2199134456, 2144434640, 2091435276, 2040068541, 1990269919, 1941978013, 1895134374, 1849683334, 1805571859, 1762749396, 1721167748, 1680780941, 1641545106, 1603418369, 1566360745, 1530334038, 1495301749, 1461228987, 1428082386, 1395830031, 1364441376, 1333887186, 1304139462, 1275171382, 1246957246, 1219472416, 1192693268, 1166597139, 1141162284, 1116367830, 1092193734, 1068620745, 1045630364, 1023204815, 1001327001, 979980484, 959149447, 938818666, 918973488, 899599801, 880684010, 862213015, 844174190, 826555361, 809344783, 792531129, 776103466, 760051238, 744364253, 729032667, 714046967, 699397960, 685076758, 671074767, 657383672, 643995429, 630902252, 618096606, 605571190, 593318936, 581332995, 569606729, 558133703, 546907679, 535922607, 525172618, 514652017, 504355277, 494277033, 484412074, 474755342, 465301923, 456047039, 446986052, 438114449, 429427846, 420921977, 412592696, 404435966, 396447861, 388624561, 380962347, 373457598, 366106788, 358906485, 351853343, 344944105, 338175597]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 627).prefactor = (1298254858981459/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 627).cutoff/(generalMeanRows 627).c)).2 =
    (96444222042447/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 627).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 627).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 627).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 627

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 627).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 627).criticalRate j.val*(generalMeanRows 627).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 627).c*(generalMeanRows 627).criticalPoint j.val)).2-
      (generalMeanRows 627).J/2-(generalMeanRows 627).error (generalMeanGrid j.val)+
      (generalMeanRows 627).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 627).c)).2-
      (generalMeanRows 627).J/2-(generalMeanRows 627).error 4 := by
  have he : (generalMeanRows 627).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 627) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 627)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0627

/-! Kernel-checked entropy margins for general spectral rectangle 628. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0628
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5607377582, 5422814868, 5246427828, 5077749930, 4916347630, 4761817499, 4613783645, 4471895419, 4335825350, 4205267283, 4079934710, 3959559246, 3843889261, 3732688628, 3625735586, 3522821704, 3423750933, 3328338737, 3236411299, 3147804789, 3062364694, 2979945195, 2900408601, 2823624818, 2749470862, 2677830411, 2608593381, 2541655543, 2476918162, 2414287660, 2353675307, 2294996927, 2238172635, 2183126578, 2129786701, 2078084533, 2027954973, 1979336104, 1932169012, 1886397617, 1841968515, 1798830831, 1756936080, 1716238036, 1676692612, 1638257743, 1600893278, 1564560881, 1529223932, 1494847440, 1461397957, 1428843499, 1397153470, 1366298591, 1336250836, 1306983363, 1278470463, 1250687497, 1223610844, 1197217854, 1171486800, 1146396829, 1121927924, 1098060865, 1074777187, 1052059146, 1029889686, 1008252405, 987131528, 966511874, 946378832, 926718331, 907516821, 888761245, 870439021, 852538015, 835046529, 817953275, 801247360, 784918271, 768955855, 753350305, 738092148, 723172224, 708581683, 694311963, 680354784, 666702131, 653346251, 640279635, 627495012, 614985339, 602743792, 590763758, 579038824, 567562773, 556329576, 545333381, 534568511, 524029455, 513710864, 503607541, 493714440, 484026658, 474539430, 465248124, 456148239, 447235395, 438505335, 429953916, 421577108, 413370988, 405331737, 397455639, 389739073, 382178516, 374770531, 367511775, 360398987, 353428989, 346598685]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 628).prefactor = (5040870160022971/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 628).cutoff/(generalMeanRows 628).c)).2 =
    (49280014170937/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 628).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 628).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 628).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 628

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 628).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 628).criticalRate j.val*(generalMeanRows 628).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 628).c*(generalMeanRows 628).criticalPoint j.val)).2-
      (generalMeanRows 628).J/2-(generalMeanRows 628).error (generalMeanGrid j.val)+
      (generalMeanRows 628).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 628).c)).2-
      (generalMeanRows 628).J/2-(generalMeanRows 628).error 4 := by
  have he : (generalMeanRows 628).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 628) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 628)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0628

/-! Kernel-checked entropy margins for general spectral rectangle 629. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0629
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def errorNumerators : Fin 121 → ℤ :=
  ![5841903700, 5655295613, 5476899404, 5306245448, 5142897390, 4986449242, 4836522789, 4692765267, 4554847283, 4422460940, 4295318145, 4173149080, 4055700815, 3942736047, 3834031956, 3729379153, 3628580730, 3531451380, 3437816595, 3347511930, 3260382323, 3176281473, 3095071261, 3016621219, 2940808040, 2867515119, 2796632135, 2728054656, 2661683779, 2597425789, 2535191847, 2474897697, 2416463393, 2359813045, 2304874581, 2251579529, 2199862803, 2149662517, 2100919798, 2053578619, 2007585641, 1962890061, 1919443474, 1877199741, 1836114869, 1796146890, 1757255755, 1719403235, 1682552817, 1646669621, 1611720311, 1577673017, 1544497256, 1512163864, 1480644927, 1449913719, 1419944641, 1390713165, 1362195781, 1334369946, 1307214038, 1280707309, 1254829842, 1229562516, 1204886962, 1180785528, 1157241250, 1134237813, 1111759524, 1089791285, 1068318561, 1047327358, 1026804195, 1006736083, 987110505, 967915388, 949139092, 930770382, 912798418, 895212734, 878003221, 861160113, 844673975, 828535683, 812736417, 797267644, 782121108, 767288819, 752763040, 738536280, 724601281, 710951011, 697578654, 684477600, 671641440, 659063957, 646739118, 634661067, 622824118, 611222751, 599851603, 588705463, 577779269, 567068098, 556567164, 546271813, 536177517, 526279871, 516574588, 507057495, 497724529, 488571732, 479595253, 470791336, 462156323, 453686648, 445378836, 437229500, 429235334, 421393116, 413699703]

private def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 629).prefactor = (2538200504503793/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 629).cutoff/(generalMeanRows 629).c)).2 =
    (204902314954303/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 629).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 629).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 629).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 629

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 629).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 629).criticalRate j.val*(generalMeanRows 629).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 629).c*(generalMeanRows 629).criticalPoint j.val)).2-
      (generalMeanRows 629).J/2-(generalMeanRows 629).error (generalMeanGrid j.val)+
      (generalMeanRows 629).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 629).c)).2-
      (generalMeanRows 629).J/2-(generalMeanRows 629).error 4 := by
  have he : (generalMeanRows 629).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 629) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 629)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0629

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock08 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 8 i) := by
  fin_cases i
  · exact EntropyRow0560.numerical
  · exact EntropyRow0561.numerical
  · exact EntropyRow0562.numerical
  · exact EntropyRow0563.numerical
  · exact EntropyRow0564.numerical
  · exact EntropyRow0565.numerical
  · exact EntropyRow0566.numerical
  · exact EntropyRow0567.numerical
  · exact EntropyRow0568.numerical
  · exact EntropyRow0569.numerical
  · exact EntropyRow0570.numerical
  · exact EntropyRow0571.numerical
  · exact EntropyRow0572.numerical
  · exact EntropyRow0573.numerical
  · exact EntropyRow0574.numerical
  · exact EntropyRow0575.numerical
  · exact EntropyRow0576.numerical
  · exact EntropyRow0577.numerical
  · exact EntropyRow0578.numerical
  · exact EntropyRow0579.numerical
  · exact EntropyRow0580.numerical
  · exact EntropyRow0581.numerical
  · exact EntropyRow0582.numerical
  · exact EntropyRow0583.numerical
  · exact EntropyRow0584.numerical
  · exact EntropyRow0585.numerical
  · exact EntropyRow0586.numerical
  · exact EntropyRow0587.numerical
  · exact EntropyRow0588.numerical
  · exact EntropyRow0589.numerical
  · exact EntropyRow0590.numerical
  · exact EntropyRow0591.numerical
  · exact EntropyRow0592.numerical
  · exact EntropyRow0593.numerical
  · exact EntropyRow0594.numerical
  · exact EntropyRow0595.numerical
  · exact EntropyRow0596.numerical
  · exact EntropyRow0597.numerical
  · exact EntropyRow0598.numerical
  · exact EntropyRow0599.numerical
  · exact EntropyRow0600.numerical
  · exact EntropyRow0601.numerical
  · exact EntropyRow0602.numerical
  · exact EntropyRow0603.numerical
  · exact EntropyRow0604.numerical
  · exact EntropyRow0605.numerical
  · exact EntropyRow0606.numerical
  · exact EntropyRow0607.numerical
  · exact EntropyRow0608.numerical
  · exact EntropyRow0609.numerical
  · exact EntropyRow0610.numerical
  · exact EntropyRow0611.numerical
  · exact EntropyRow0612.numerical
  · exact EntropyRow0613.numerical
  · exact EntropyRow0614.numerical
  · exact EntropyRow0615.numerical
  · exact EntropyRow0616.numerical
  · exact EntropyRow0617.numerical
  · exact EntropyRow0618.numerical
  · exact EntropyRow0619.numerical
  · exact EntropyRow0620.numerical
  · exact EntropyRow0621.numerical
  · exact EntropyRow0622.numerical
  · exact EntropyRow0623.numerical
  · exact EntropyRow0624.numerical
  · exact EntropyRow0625.numerical
  · exact EntropyRow0626.numerical
  · exact EntropyRow0627.numerical
  · exact EntropyRow0628.numerical
  · exact EntropyRow0629.numerical
end SingularValueBounds.KL.Certificates
